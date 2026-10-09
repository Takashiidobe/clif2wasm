//! Every opcode in the pinned Cranelift must have a reviewed status in
//! `tests/opcode_coverage.txt`, so upgrading Cranelift or changing its features
//! fails here until the new opcodes are classified.

use std::collections::BTreeMap;

use cranelift_codegen::ir::Opcode;

fn registry() -> BTreeMap<String, (String, String)> {
    let text = std::fs::read_to_string("tests/opcode_coverage.txt").unwrap();
    let mut entries = BTreeMap::new();
    for line in text
        .lines()
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
    {
        let mut parts = line.splitn(3, ' ');
        let opcode = parts.next().unwrap().to_owned();
        let status = parts
            .next()
            .unwrap_or_else(|| panic!("`{line}` has no status"))
            .to_owned();
        let note = parts.next().unwrap_or("").to_owned();
        assert!(
            entries.insert(opcode.clone(), (status, note)).is_none(),
            "duplicate registry entry `{opcode}`"
        );
    }
    entries
}

#[test]
fn every_cranelift_opcode_has_a_reviewed_status() {
    let registry = registry();
    let all: Vec<String> = Opcode::all().iter().map(|op| op.to_string()).collect();
    let missing: Vec<_> = all
        .iter()
        .filter(|op| !registry.contains_key(*op))
        .collect();
    assert!(
        missing.is_empty(),
        "opcodes missing from tests/opcode_coverage.txt (classify them): {missing:?}"
    );
    let stale: Vec<_> = registry.keys().filter(|op| !all.contains(op)).collect();
    assert!(
        stale.is_empty(),
        "registry entries for opcodes Cranelift no longer has: {stale:?}"
    );
}

#[test]
fn registry_statuses_are_valid_and_explained() {
    for (opcode, (status, note)) in registry() {
        assert!(
            matches!(
                status.as_str(),
                "lowered" | "erased" | "partial" | "unsupported"
            ),
            "`{opcode}` has unknown status `{status}`"
        );
        if matches!(status.as_str(), "partial" | "unsupported") {
            assert!(!note.is_empty(), "`{opcode}` is {status} without a note");
        }
    }
}

#[test]
fn immediate_and_complement_forms_are_not_exposed() {
    let exposed: Vec<String> = Opcode::all()
        .iter()
        .map(|op| op.to_string())
        .filter(|name| name.ends_with("_imm") || name.ends_with("_not"))
        .collect();
    assert!(
        exposed.is_empty(),
        "Cranelift now exposes immediate/complement forms; lower them and update docs/opcode-coverage.md: {exposed:?}"
    );
}
