//! No request-derived text ever reaches a SQL string: every `fossil sql`
//! argument equals one of the module's constants, for any page name.
mod common;
use common::{FakeFossil, bound, isolated_fossil, parse, real_repo, wargs};
use fossil_mcp::server::types::{CommitState, Publication};
use fossil_mcp::server::{ATTRIBUTION_SQL, valid_page_name};
use fossil_mcp::{FossilWiki, WikiConfig};
use proptest::prelude::*;
use std::fs;
use std::os::unix::fs::PermissionsExt;

const NASTY: &[&str] = &[
    "P'; SELECT 42; --",
    "a'b''c",
    "semi;colon",
    "pipe|name",
    "a/b/c",
    "caf\u{e9} \u{2603} \u{1f600}",
    "100%_like",
    "back\\slash",
    "\"dq\"",
    "x') OR ('1'='1",
];

fn assert_sql_fixed(calls: Vec<(Vec<String>, Vec<u8>)>) {
    assert!(!calls.is_empty(), "attribution must run a sql query");
    for (argv, _) in calls {
        let sql = argv.last().unwrap();
        assert!(
            ATTRIBUTION_SQL.contains(&sql.as_str()),
            "sql not from the fixed set: {sql}"
        );
        assert_eq!(
            argv.iter().filter(|a| a.as_str() == "sql").count(),
            1,
            "{argv:?}"
        );
    }
}

#[tokio::test]
async fn nasty_page_names_never_reach_sql_fake() {
    for (i, name) in NASTY.iter().enumerate() {
        let f = FakeFossil::new();
        let w = bound(&f, |_| {}).await;
        let r = w
            .write_wiki_page(wargs(&format!("op{i}"), name, "v1", Publication::LocalOnly))
            .await
            .unwrap();
        let rc = parse(&r).receipt.unwrap();
        assert_eq!(rc.commit_state, CommitState::Committed, "{name}");
        assert!(rc.revision.is_some(), "{name}: {rc:?}");
        assert_sql_fixed(f.calls_to("sql"));
    }
}

#[tokio::test]
async fn nasty_page_names_with_real_fossil_are_attributed_via_fixed_sql() {
    let (repo, bin, dir) = real_repo();
    let log = dir.path().join("sql.log");
    let wrapper = dir.path().join("recording-fossil");
    fs::write(
        &wrapper,
        format!(
            "#!/bin/sh\nif [ \"$1\" = sql ]; then for a; do l=\"$a\"; done; printf '%s\\n' \"$l\" >> '{}'; fi\nexec '{}' \"$@\"\n",
            log.display(),
            bin.display()
        ),
    )
    .unwrap();
    fs::set_permissions(&wrapper, fs::Permissions::from_mode(0o755)).unwrap();
    let mut cfg = WikiConfig::new("itest", &repo);
    cfg.fossil_bin = wrapper;
    cfg.allow_local_writes = true;
    cfg.state_dir = Some(dir.path().join("state"));
    let w = FossilWiki::bind(cfg).await.unwrap();
    for (i, name) in NASTY.iter().enumerate() {
        let r = w
            .write_wiki_page(wargs(
                &format!("op{i}"),
                name,
                "body",
                Publication::LocalOnly,
            ))
            .await
            .unwrap();
        let rc = parse(&r).receipt.unwrap();
        assert!(rc.revision.is_some(), "{name}: {rc:?}");
    }
    let seen = fs::read_to_string(&log).unwrap();
    assert!(seen.lines().count() >= NASTY.len());
    for l in seen.lines() {
        assert!(
            ATTRIBUTION_SQL.contains(&l),
            "sql not from the fixed set: {l}"
        );
    }
    let _ = isolated_fossil; // fixture re-exported for sibling tests
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]
    #[test]
    fn arbitrary_page_names_never_reach_sql(name in ".{1,40}") {
        prop_assume!(valid_page_name(&name));
        let rt = tokio::runtime::Builder::new_current_thread().enable_all().build().unwrap();
        rt.block_on(async {
            let f = FakeFossil::new();
            let w = bound(&f, |_| {}).await;
            let r = w.write_wiki_page(wargs("op", &name, "v", Publication::LocalOnly)).await.unwrap();
            let rc = parse(&r).receipt.unwrap();
            assert_eq!(rc.commit_state, CommitState::Committed);
            assert_sql_fixed(f.calls_to("sql"));
        });
    }
}
