"""Accept only the logical axioms of the compiled theorem endpoints.

Usage: check_axioms.py LOG [AUDIT_SOURCE ...]
Default: CheckAxioms.lean for a small standalone smoke test.

The reference floor is the 199 different declarations checked by the
successful CI build of 14 October 2026. New proofs may add checks; a
deliberate removal requires an explicit change to this floor.
"""
from collections import Counter
from pathlib import Path
import re
import sys

log = Path(sys.argv[1]).read_text()
sources = sys.argv[2:] or ["CheckAxioms.lean"]

expected = Counter()
for source in sources:
    expected.update(re.findall(
        r"^#print axioms (\S+)", Path(source).read_text(), re.M))
assert expected, "No declarations were requested for the axiom audit"
# The small standalone smoke test intentionally runs with fewer endpoints.
if len(sources) > 1:
    assert len(expected) >= 199, (
        f"Audit regressed from 199 unique endpoints to {len(expected)}")

reports = []
found_axioms = {}
for name, axioms in re.findall(
        r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
    reports.append(name)
    found_axioms[name] = {a.strip() for a in axioms.split(",") if a.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
    reports.append(name)
    found_axioms[name] = set()

observed = Counter(reports)
assert observed == expected, (
    f"Missing or extra axiom reports: expected={expected - observed}; "
    f"unexpected={observed - expected}")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in found_axioms.items():
    assert axioms <= allowed, (
        f"Unexpected axioms in {name}: {axioms - allowed}")
print(f"Checked {len(found_axioms)} declarations "
      f"({sum(observed.values())} certificates); "
      "only the standard logical axioms occur.")
