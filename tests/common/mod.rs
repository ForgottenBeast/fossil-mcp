//! Shared fixtures: fake `fossil` executables and throwaway real repositories.
//! Nothing here touches a real wiki; every path lives under a `TempDir`.
#![allow(dead_code)]

use fossil_mcp::server::types::{Publication, WriteWikiPageArgs};
use fossil_mcp::{FossilWiki, WikiConfig, WriteToolOutput};
use rmcp::handler::server::wrapper::Parameters;
use rmcp::model::CallToolResult;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};

/// A scripted stand-in for the `fossil` binary.
///
/// It records argv/stdin of every call under `calls/`, keeps one page's
/// head/parent revision, and runs an optional `on_<subcommand>` snippet
/// (sourced by `sh`) so tests can inject faults deterministically.
pub struct FakeFossil {
    pub dir: tempfile::TempDir,
    pub bin: PathBuf,
}

const SCRIPT: &str = r#"#!/bin/sh
D="__DIR__"
id=$$
mkdir -p "$D/calls"
sub=""
for a in "$@"; do
  case "$a" in
    create|commit|info|artifact|sql) [ -z "$sub" ] && sub="$a" ;;
    sync) [ -z "$sub" ] && sub=sync ;;
    get) [ -z "$sub" ] && sub=get ;;
    list) [ -z "$sub" ] && sub=list ;;
  esac
done
: > "$D/calls/$id.argv"
for a in "$@"; do printf '%s\n' "$a" >> "$D/calls/$id.argv"; done
echo "$sub" > "$D/calls/$id.sub"
ph=77696B692D$(printf %s "$3" | od -An -tx1 | tr -d ' \n' | tr 'a-f' 'A-F')
echo $id > "$D/pid.$sub"
if [ "$sub" = create ] || [ "$sub" = commit ]; then cat > "$D/calls/$id.stdin"; fi
if [ -f "$D/on_$sub" ]; then . "$D/on_$sub"; fi
case "$sub" in
  create|commit)
    prevu=$(cat "$D/uuid" 2>/dev/null)
    [ -f "$D/uuid" ] && cp "$D/uuid" "$D/parent"
    echo "u$id" > "$D/uuid"
    rid=$(( $(cat "$D/rid" 2>/dev/null || echo 0) + 1 )); echo $rid > "$D/rid"
    [ -f "$D/hide_ours" ] || echo "$rid|u$id|$prevu|$ph" >> "$D/revs"
    cp "$D/calls/$id.stdin" "$D/content"
    echo "ok"
    ;;
  get)
    if [ -f "$D/uuid" ]; then
      p=""; [ -f "$D/parent" ] && p=$(cat "$D/parent")
      [ -f "$D/force_parent" ] && p=$(cat "$D/force_parent")
      h=$(cat "$D/uuid"); [ -f "$D/head_override" ] && h=$(cat "$D/head_override")
      printf '{"payload":{"name":"P","uuid":"%s","parent":"%s","content":"x"}}\n' "$h" "$p"
    else
      printf '{"resultCode":"FOSSIL-3006","resultText":"Wiki page not found"}\n'
    fi
    ;;
  list) echo HomePage ;;
  info)
    echo "project-name: fixture"
    if [ -f "$D/project_code" ]; then echo "project-code: $(cat "$D/project_code")"; else echo "project-code: PC1"; fi
    ;;
  sql)
    # Emulates the module's fixed wiki-revision query: 'hex(tagname)',rid,'uuid','parent' (quote mode)
    if [ -f "$D/revs" ]; then
      sort -t'|' -k1 -nr "$D/revs" | while IFS='|' read -r r u p h; do echo "'$h',$r,'$u','$p'"; done
    fi
    ;;
  artifact)
    [ -f "$D/missing_artifact" ] && exit 1
    u=""
    while [ $# -gt 0 ]; do
      if [ "$1" = artifact ]; then u="$2"; break; fi
      shift
    done
    if [ -f "$D/artifact_$u" ]; then cat "$D/artifact_$u"
    elif [ -f "$D/uuid" ] && [ "$u" = "$(cat "$D/uuid")" ]; then
      printf 'D t\nL P\nU fx\nW %s\n' "$(wc -c < "$D/content" | tr -d ' ')"
      cat "$D/content"
      printf '\nZ 00\n'
    else exit 1; fi
    ;;
  sync) echo "Round-trips: 1   Artifacts sent: 1  received: 0" ;;
esac
exit 0
"#;

impl FakeFossil {
    pub fn new() -> Self {
        let dir = tempfile::tempdir().unwrap();
        let bin = dir.path().join("fossil");
        fs::write(
            &bin,
            SCRIPT.replace("__DIR__", dir.path().to_str().unwrap()),
        )
        .unwrap();
        fs::set_permissions(&bin, fs::Permissions::from_mode(0o755)).unwrap();
        settle(&bin);
        for e in fs::read_dir(dir.path().join("calls"))
            .into_iter()
            .flatten()
            .flatten()
        {
            let _ = fs::remove_file(e.path());
        }
        let _ = fs::remove_file(dir.path().join("pid."));
        Self { dir, bin }
    }

    /// Install a shell snippet that runs when `sub` is invoked.
    pub fn on(&self, sub: &str, snippet: &str) {
        fs::write(self.dir.path().join(format!("on_{sub}")), snippet).unwrap();
    }

    /// Recorded calls as (subcommand, argv, stdin) for every invocation.
    pub fn calls(&self) -> Vec<(String, Vec<String>, Vec<u8>)> {
        let mut out = vec![];
        let Ok(rd) = fs::read_dir(self.dir.path().join("calls")) else {
            return out;
        };
        for e in rd.flatten() {
            let p = e.path();
            if p.extension().is_some_and(|x| x == "argv") {
                let sub = fs::read_to_string(p.with_extension("sub")).unwrap_or_default();
                let argv = fs::read_to_string(&p)
                    .unwrap()
                    .lines()
                    .map(String::from)
                    .collect();
                let stdin = fs::read(p.with_extension("stdin")).unwrap_or_default();
                out.push((sub.trim().to_string(), argv, stdin));
            }
        }
        out
    }

    pub fn calls_to(&self, sub: &str) -> Vec<(Vec<String>, Vec<u8>)> {
        self.calls()
            .into_iter()
            .filter(|c| c.0 == sub)
            .map(|c| (c.1, c.2))
            .collect()
    }

    pub fn file(&self, name: &str) -> PathBuf {
        self.dir.path().join(name)
    }

    /// A placeholder repository file so binding validation sees a regular file.
    pub fn repo_file(&self) -> PathBuf {
        let p = self.dir.path().join("repo.fossil");
        fs::write(&p, b"not-a-real-repo").unwrap();
        p
    }
}

/// Wait out ETXTBSY: a script just written can still be held open for write by
/// a concurrently forked sibling test until that child execs.
fn settle(bin: &Path) {
    for _ in 0..200 {
        match std::process::Command::new(bin)
            .arg("--settle-probe")
            .output()
        {
            Err(e) if e.raw_os_error() == Some(26) => {
                std::thread::sleep(std::time::Duration::from_millis(10))
            }
            _ => return,
        }
    }
    panic!("script stayed busy");
}

/// Wrapper script that runs the real `fossil` with an isolated HOME.
pub fn isolated_fossil(dir: &Path) -> PathBuf {
    let real = which("fossil").expect("fossil binary must be on PATH for integration tests");
    let home = dir.join("home");
    fs::create_dir_all(&home).unwrap();
    let bin = dir.join("fossil-isolated");
    fs::write(
        &bin,
        format!(
            "#!/bin/sh\nHOME='{}' XDG_CONFIG_HOME='{}' USER=fixture LOGNAME=fixture exec '{}' \"$@\"\n",
            home.display(),
            home.display(),
            real.display()
        ),
    )
    .unwrap();
    fs::set_permissions(&bin, fs::Permissions::from_mode(0o755)).unwrap();
    settle(&bin);
    bin
}

pub fn which(name: &str) -> Option<PathBuf> {
    std::env::var_os("PATH")?
        .to_string_lossy()
        .split(':')
        .map(|d| Path::new(d).join(name))
        .find(|p| p.is_file())
}

/// Create a throwaway Fossil repository; returns (repo path, isolated bin, tempdir).
pub fn real_repo() -> (PathBuf, PathBuf, tempfile::TempDir) {
    let dir = tempfile::tempdir().unwrap();
    let bin = isolated_fossil(dir.path());
    let repo = dir.path().join("test.fossil");
    let st = std::process::Command::new(&bin)
        .arg("new")
        .arg("--admin-user")
        .arg("fixture")
        .arg(&repo)
        .output()
        .expect("fossil new");
    assert!(
        st.status.success(),
        "fossil new failed: {}",
        String::from_utf8_lossy(&st.stderr)
    );
    (repo, bin, dir)
}

/// Bind a wiki to the fake fossil. `tweak` adjusts the config.
pub async fn bound(f: &FakeFossil, tweak: impl FnOnce(&mut WikiConfig)) -> FossilWiki {
    let mut cfg = WikiConfig::new("repo1", f.repo_file());
    cfg.fossil_bin = f.bin.clone();
    cfg.allow_local_writes = true;
    cfg.state_dir = Some(f.dir.path().join("state"));
    tweak(&mut cfg);
    FossilWiki::bind(cfg).await.expect("bind")
}

pub fn wargs(
    op: &str,
    page: &str,
    content: &str,
    publication: Publication,
) -> Parameters<WriteWikiPageArgs> {
    Parameters(WriteWikiPageArgs {
        operation_id: op.into(),
        page_name: page.into(),
        content: content.into(),
        mimetype: None,
        publication,
    })
}

/// Parse the structured body of a write-family tool result.
pub fn parse(r: &CallToolResult) -> WriteToolOutput {
    serde_json::from_value(r.structured_content.clone().expect("structured content")).unwrap()
}

pub fn is_error(r: &CallToolResult) -> bool {
    r.is_error == Some(true)
}
