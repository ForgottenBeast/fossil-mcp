//! Opaque secrets and the sources they are read from.
//!
//! A [`Secret`] holds bytes that must never be logged, displayed, serialized
//! or copied into error text: it has no `Display` or `Serialize`, its `Debug`
//! prints a fixed marker and the buffer is zeroized on drop. Credentials come
//! from a file path given on the command line through a [`SecretSource`];
//! never from the environment, never from a tool argument.
//!
//! Residual exposure, accepted: a parser that has to decode the secret (JSON
//! unescaping, the PEM reader inside the signing library, the HTTP stack that
//! carries a bearer header) may hold transient copies that this crate cannot
//! zeroize.

use serde::Deserialize;
use std::fs::OpenOptions;
use std::io::Read;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use zeroize::{Zeroize, Zeroizing};

/// Largest accepted secret file in bytes.
pub const MAX_SECRET_BYTES: u64 = 16 * 1024;

/// Bytes that must not leak. See the module documentation.
#[derive(Clone)]
pub struct Secret(Zeroizing<Vec<u8>>);

impl Secret {
    /// Takes ownership of `bytes` (no copy is made).
    pub fn new(bytes: Vec<u8>) -> Self {
        Self(Zeroizing::new(bytes))
    }

    /// The secret bytes. Callers must not log or format them.
    pub fn expose(&self) -> &[u8] {
        &self.0
    }
}

impl std::fmt::Debug for Secret {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Secret(<redacted>)")
    }
}

/// Why a secret could not be produced. Messages are fixed and carry no path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SecretError {
    /// The source could not be read.
    Unreadable,
    /// The file is a symlink, not a regular file, too large or accessible by
    /// others.
    Unsafe,
    /// The content is not a valid key document.
    Invalid,
}

impl std::fmt::Display for SecretError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Unreadable => "the secret source could not be read",
            Self::Unsafe => "the secret file is a symlink, oversize or accessible by others",
            Self::Invalid => "the secret content is not valid",
        })
    }
}

impl std::error::Error for SecretError {}

/// Where a secret comes from. `read` is called again on every token refresh,
/// so a rotated credential is picked up without a restart.
pub trait SecretSource: Send + Sync {
    /// Read the current secret.
    fn read(&self) -> Result<Secret, SecretError>;
}

/// Reads a secret from a regular file.
///
/// The file must not be a symlink (checked on the opened descriptor, not on
/// the path), must be at most [`MAX_SECRET_BYTES`], and must grant nothing to
/// "others" nor write access to the group. Group read (0640) is accepted: the
/// deployed key is owned by a service account with the operator in its group.
#[derive(Debug, Clone)]
pub struct FileSecretSource {
    path: PathBuf,
}

impl FileSecretSource {
    /// A source reading `path` on every call.
    pub fn new(path: impl AsRef<Path>) -> Self {
        Self {
            path: path.as_ref().to_path_buf(),
        }
    }
}

impl SecretSource for FileSecretSource {
    fn read(&self) -> Result<Secret, SecretError> {
        let mut file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
            .open(&self.path)
            .map_err(|e| match e.raw_os_error() {
                Some(libc::ELOOP) => SecretError::Unsafe,
                _ => SecretError::Unreadable,
            })?;
        let meta = file.metadata().map_err(|_| SecretError::Unreadable)?;
        if !meta.is_file() || meta.mode() & 0o027 != 0 || meta.len() > MAX_SECRET_BYTES {
            return Err(SecretError::Unsafe);
        }
        let mut buf = Zeroizing::new(Vec::with_capacity(meta.len() as usize));
        // One byte past the cap catches a file that grew after fstat.
        (&mut file)
            .take(MAX_SECRET_BYTES + 1)
            .read_to_end(&mut buf)
            .map_err(|_| SecretError::Unreadable)?;
        if buf.len() as u64 > MAX_SECRET_BYTES {
            return Err(SecretError::Unsafe);
        }
        Ok(Secret::new(std::mem::take(&mut *buf)))
    }
}

/// A Zitadel machine-user key (`{"type":"serviceaccount","keyId","key","userId"}`).
pub struct ZitadelKey {
    key_id: String,
    user_id: String,
    private_key_pem: Secret,
}

#[derive(Deserialize)]
struct KeyDocument {
    #[serde(rename = "type")]
    kind: String,
    #[serde(rename = "keyId")]
    key_id: String,
    #[serde(rename = "userId")]
    user_id: String,
    key: String,
}

impl ZitadelKey {
    /// Parse a key document. Errors never include document content.
    pub fn parse(secret: &Secret) -> Result<Self, SecretError> {
        let mut doc: KeyDocument =
            serde_json::from_slice(secret.expose()).map_err(|_| SecretError::Invalid)?;
        if doc.kind != "serviceaccount"
            || doc.key_id.is_empty()
            || doc.user_id.is_empty()
            || doc.key.is_empty()
        {
            doc.key.zeroize();
            return Err(SecretError::Invalid);
        }
        Ok(Self {
            key_id: std::mem::take(&mut doc.key_id),
            user_id: std::mem::take(&mut doc.user_id),
            private_key_pem: Secret::new(std::mem::take(&mut doc.key).into_bytes()),
        })
    }

    /// Key id, sent as the JWT `kid`.
    pub fn key_id(&self) -> &str {
        &self.key_id
    }

    /// Machine user id (the assertion's `iss` and `sub`).
    pub fn user_id(&self) -> &str {
        &self.user_id
    }

    /// The PEM-encoded RSA private key.
    pub(crate) fn private_key_pem(&self) -> &Secret {
        &self.private_key_pem
    }
}

impl std::fmt::Debug for ZitadelKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ZitadelKey")
            .field("key_id", &self.key_id)
            .field("user_id", &self.user_id)
            .field("private_key_pem", &self.private_key_pem)
            .finish()
    }
}
