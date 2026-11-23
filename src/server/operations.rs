//! Private receipt journal for idempotent writes.
//!
//! One JSON record per operation id under `<state>/ops/`, written via a
//! private temporary file (0600) + fsync + atomic rename + directory fsync.
//! The journal holds bounded exact request bytes for replay equality; those
//! bytes are sensitive retained data and never appear in `Debug`, logs, status
//! or errors. A single `LOCK` file (exclusive create) admits one owner process;
//! a stale lock fails closed and needs operator confirmation.
//!
//! A journal and a Fossil commit are not one transaction: the guarantee is
//! at-most-once *automatic* submission with a conservative `unknown`, not
//! exactly-once.

use crate::server::types::{
    CommitState, ErrorCode, MAX_OPERATION_ID_BYTES, Publication, PublicationState, RECEIPT_VERSION,
    RetryAction, WikiMimetype, WriteReceipt,
};
use serde::{Deserialize, Serialize};
use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};

/// Default journal size cap (payload + receipts): 64 MiB.
pub const DEFAULT_JOURNAL_CAP: u64 = 64 << 20;

/// Exact request retained for replay comparison.
#[derive(Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct StoredRequest {
    /// Target page.
    pub page_name: String,
    /// Exact content bytes (sensitive).
    pub content: String,
    /// Requested MIME type.
    pub mimetype: Option<WikiMimetype>,
    /// Requested publication mode.
    pub publication: Publication,
}

impl std::fmt::Debug for StoredRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StoredRequest")
            .field("content_len", &self.content.len())
            .field("publication", &self.publication)
            .finish_non_exhaustive()
    }
}

/// One persisted operation.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Record {
    /// Record format version.
    pub version: u32,
    /// Binding alias the record belongs to.
    pub repo_id: String,
    /// Retained request.
    pub request: StoredRequest,
    /// Latest receipt.
    pub receipt: WriteReceipt,
}

impl Record {
    /// A reservation written *before* any child is spawned: commit is already
    /// `unknown`, so a crash at any later point can never read as "not done".
    pub fn reservation(repo_id: &str, operation_id: &str, request: StoredRequest) -> Self {
        let wants = request.publication == Publication::SyncRepository;
        let receipt = WriteReceipt {
            receipt_version: RECEIPT_VERSION,
            repo_id: repo_id.to_string(),
            operation_id: operation_id.to_string(),
            page_name: request.page_name.clone(),
            previous_revision: None,
            revision: None,
            commit_state: CommitState::Unknown,
            publication_state: if wants {
                PublicationState::Unknown
            } else {
                PublicationState::NotRequested
            },
            error_code: Some(ErrorCode::CommitUnconfirmed),
            retry_action: RetryAction::Reconcile,
        };
        Self {
            version: RECEIPT_VERSION,
            repo_id: repo_id.to_string(),
            request,
            receipt,
        }
    }
}

/// Journal failures; all map to `receipt_store_unavailable`.
#[derive(Debug, PartialEq, Eq)]
pub enum JournalError {
    /// Directory missing, wrong mode, symlink, or I/O failure.
    Unavailable,
    /// Another process holds (or crashed holding) the lock.
    Locked,
    /// Record is truncated, corrupt or of an unknown version.
    Corrupt,
    /// The size cap would be exceeded.
    Full,
    /// The operation id is not a valid key.
    BadKey,
}

/// Handle on an opened, locked journal directory.
#[derive(Debug)]
pub struct Journal {
    ops: PathBuf,
    tmp: PathBuf,
    lock: PathBuf,
    cap: u64,
}

/// Validate an operation id: 1-64 ASCII letters, digits, `_` or `-`.
pub fn valid_operation_id(id: &str) -> bool {
    !id.is_empty()
        && id.len() <= MAX_OPERATION_ID_BYTES
        && id
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-')
}

fn fsync_dir(p: &Path) -> Result<(), JournalError> {
    File::open(p)
        .and_then(|d| d.sync_all())
        .map_err(|_| JournalError::Unavailable)
}

fn private_dir(p: &Path) -> Result<(), JournalError> {
    match fs::symlink_metadata(p) {
        Ok(m) => {
            if m.file_type().is_symlink() || !m.is_dir() {
                return Err(JournalError::Unavailable);
            }
            if m.mode() & 0o077 != 0 {
                return Err(JournalError::Unavailable);
            }
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            fs::DirBuilder::new()
                .mode(0o700)
                .create(p)
                .map_err(|_| JournalError::Unavailable)?;
        }
        Err(_) => return Err(JournalError::Unavailable),
    }
    Ok(())
}

impl Journal {
    /// Open (creating if needed) the journal in `state_dir` and take its lock.
    pub fn open(state_dir: &Path, cap: u64) -> Result<Self, JournalError> {
        private_dir(state_dir)?;
        let ops = state_dir.join("ops");
        let tmp = state_dir.join("tmp");
        let lock = state_dir.join("LOCK");
        private_dir(&ops)?;
        private_dir(&tmp)?;
        match OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&lock)
        {
            Ok(mut f) => {
                let _ = writeln!(f, "{}", std::process::id());
            }
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
                return Err(JournalError::Locked);
            }
            Err(_) => return Err(JournalError::Unavailable),
        }
        let j = Self {
            ops,
            tmp,
            lock,
            cap,
        };
        // Staging remnants from a crashed predecessor are classified and
        // removed: they are journal scaffolding, never wiki input.
        if let Ok(rd) = fs::read_dir(&j.tmp) {
            for e in rd.flatten() {
                let _ = fs::remove_file(e.path());
            }
        }
        Ok(j)
    }

    fn path(&self, id: &str) -> Result<PathBuf, JournalError> {
        if !valid_operation_id(id) {
            return Err(JournalError::BadKey);
        }
        Ok(self.ops.join(format!("{id}.json")))
    }

    /// Load the record for `id`, if any. Corrupt/unknown-version fails closed.
    pub fn get(&self, id: &str) -> Result<Option<Record>, JournalError> {
        let p = self.path(id)?;
        match fs::read(&p) {
            Ok(bytes) => {
                let rec: Record =
                    serde_json::from_slice(&bytes).map_err(|_| JournalError::Corrupt)?;
                if rec.version != RECEIPT_VERSION || rec.receipt.receipt_version != RECEIPT_VERSION
                {
                    return Err(JournalError::Corrupt);
                }
                Ok(Some(rec))
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(_) => Err(JournalError::Unavailable),
        }
    }

    fn used_bytes(&self) -> Result<u64, JournalError> {
        let mut total = 0;
        for e in fs::read_dir(&self.ops)
            .map_err(|_| JournalError::Unavailable)?
            .flatten()
        {
            total += e.metadata().map(|m| m.len()).unwrap_or(0);
        }
        Ok(total)
    }

    /// Durably store `rec` (replacing any previous record for the same id).
    pub fn put(&self, id: &str, rec: &Record) -> Result<(), JournalError> {
        let dest = self.path(id)?;
        let bytes = serde_json::to_vec(rec).map_err(|_| JournalError::Unavailable)?;
        let old = fs::metadata(&dest).map(|m| m.len()).unwrap_or(0);
        if self.used_bytes()?.saturating_sub(old) + bytes.len() as u64 > self.cap {
            return Err(JournalError::Full);
        }
        let stage = self.tmp.join(format!("{id}.{}.tmp", std::process::id()));
        let _ = fs::remove_file(&stage);
        let mut f = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&stage)
            .map_err(|_| JournalError::Unavailable)?;
        f.write_all(&bytes).map_err(|_| JournalError::Unavailable)?;
        f.sync_all().map_err(|_| JournalError::Unavailable)?;
        drop(f);
        fs::rename(&stage, &dest).map_err(|_| JournalError::Unavailable)?;
        fsync_dir(&self.ops)
    }
}

impl Drop for Journal {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.lock);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn req(content: &str) -> StoredRequest {
        StoredRequest {
            page_name: "P".into(),
            content: content.into(),
            mimetype: None,
            publication: Publication::LocalOnly,
        }
    }

    #[test]
    fn debug_never_prints_content() {
        let s = format!("{:?}", Record::reservation("r", "o", req("SECRET-BYTES")));
        assert!(!s.contains("SECRET-BYTES"), "{s}");
    }

    #[test]
    fn key_validation() {
        assert!(valid_operation_id("a-b_C9"));
        assert!(!valid_operation_id(""));
        assert!(!valid_operation_id("../x"));
        assert!(!valid_operation_id(&"a".repeat(65)));
    }

    #[test]
    fn round_trip_and_lock() {
        let d = tempfile::tempdir().unwrap();
        let st = d.path().join("state");
        let j = Journal::open(&st, DEFAULT_JOURNAL_CAP).unwrap();
        assert_eq!(
            Journal::open(&st, DEFAULT_JOURNAL_CAP).unwrap_err(),
            JournalError::Locked
        );
        let rec = Record::reservation("r", "o1", req("c"));
        j.put("o1", &rec).unwrap();
        assert_eq!(j.get("o1").unwrap(), Some(rec));
        assert_eq!(j.get("nope").unwrap(), None);
        drop(j);
        assert!(
            Journal::open(&st, DEFAULT_JOURNAL_CAP).is_ok(),
            "lock released on drop"
        );
    }
}
