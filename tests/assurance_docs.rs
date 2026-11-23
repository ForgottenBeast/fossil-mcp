//! Documentation and packaging contracts: retired assurance claims stay
//! retired, the correspondence table points at tests that exist, and the Nix
//! package is gated by its test suite. These are fixed regression checks plus
//! human review, not properties over prose.
use std::fs;
use std::path::Path;

fn read(p: &str) -> String {
    fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join(p)).unwrap()
}

#[test]
fn historical_tla_docs_lead_with_a_retirement_notice() {
    for p in [
        "TLC_VERIFICATION_REPORT.md",
        "TLA_SPECIFICATION.md",
        "WIKISIMPLE_IMPROVEMENTS.md",
        "src/WikiSimple_README.md",
        "book/src/appendices/tla-specification.md",
    ] {
        let head: String = read(p).lines().take(8).collect::<Vec<_>>().join("\n");
        assert!(
            head.contains("RETIRED - NOT A CERTIFICATION"),
            "{p} lacks the notice"
        );
    }
}

#[test]
fn no_active_false_assurance_claims_remain() {
    let intro = read("book/src/introduction.md");
    assert!(!intro.contains("117,931"), "stale proof claim");
    assert!(!intro.contains("Production Ready"));
    let report = read("TLC_VERIFICATION_REPORT.md");
    let (before, _) = report
        .split_once("## Historical content")
        .expect("history section");
    assert!(
        !before.contains("PASS") && !before.contains("correct"),
        "claims must sit under history"
    );
    let spec = read("TLA_SPECIFICATION.md");
    let (before, _) = spec
        .split_once("## Historical content")
        .expect("history section");
    assert!(
        before.contains("no** automatic-retry"),
        "must disclaim retry/force/CAS"
    );
}

#[test]
fn correspondence_table_references_existing_tests() {
    let spec = read("TLA_SPECIFICATION.md");
    let table = spec
        .split_once("## Current invariant-to-test correspondence")
        .unwrap()
        .1;
    let mut checked = 0;
    for tok in table.split('`') {
        let Some((file, func)) = tok.split_once("::") else {
            continue;
        };
        if !file.starts_with("tests/") {
            continue;
        }
        let src = read(file);
        assert!(
            src.contains(&format!("fn {func}")),
            "{file} has no fn {func}"
        );
        checked += 1;
    }
    assert!(
        checked >= 11,
        "table must reference real tests, found {checked}"
    );
}

#[test]
fn nix_package_is_gated_by_its_tests_and_pins_fossil() {
    let flake = read("flake.nix");
    let default = flake.split("default =").nth(1).unwrap();
    let default = default.split("doc = platform").next().unwrap();
    assert!(
        default.contains("doCheck = true"),
        "default package must run its tests"
    );
    assert!(!default.contains("doCheck = false"));
    assert!(default.contains("nativeCheckInputs = [ pkgs.fossil ]"));
    assert!(
        default.contains("wrapProgram"),
        "runtime fossil must be wrapped"
    );
    assert!(
        flake.contains("checks.slice1"),
        "executable check must exist"
    );
}
