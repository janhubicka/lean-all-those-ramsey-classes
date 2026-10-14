#!/usr/bin/env python3
"""Structural and source-integrity audit of the All Those Ramsey Classes library.

Execute from any working directory: python3 scripts/audit_library.py

The CI build separately compiles every module and #print axioms separately
tests theorem dependencies. This script checks the local import graph,
supported API roots, syntax-level admissions, and reports optional modules
not reachable through the curated public imports. Unreachable does NOT mean
dead: research/audit modules and their counterexamples are intentionally kept.
"""
from collections import defaultdict
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MODULE_ROOT = ROOT / "AllThoseRamseyClasses"
FILES = {
    p.relative_to(ROOT).with_suffix("").as_posix().replace("/", "."): p
    for p in MODULE_ROOT.rglob("*.lean")
}
FILES["AllThoseRamseyClasses"] = ROOT / "AllThoseRamseyClasses.lean"
for p in sorted(ROOT.glob("CheckAxioms*.lean")):
    FILES[p.stem] = p
IMPORT = re.compile(r"(?m)^\s*import\s+([A-Za-z][A-Za-z0-9_.]*)\s*$")
UNTRUSTED = re.compile(r"\b(?:sorry|sorryAx|admit)\b|\b(?:axiom|constant)\s+[A-Za-z_]")
errors = []


def executable_text(source: str) -> str:
    """Remove nested Lean comments and string contents, preserving line breaks."""
    out = []
    i = depth = 0
    in_string = False
    while i < len(source):
        c = source[i]
        if depth:
            if source.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_string:
            if c == "\\" and i + 1 < len(source):
                out.extend("  ")
                i += 2
            elif c == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif source.startswith("--", i):
            e = source.find("\n", i)
            if e < 0:
                e = len(source)
            out.extend(" " * (e - i))
            i = e
        elif source.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif c == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    if depth or in_string:
        raise ValueError("unclosed Lean comment or string")
    return "".join(out)


GRAPH = {}
for module, path in sorted(FILES.items()):
    src = path.read_text(encoding="utf-8")
    try:
        code = executable_text(src)
    except ValueError as exc:
        errors.append(f"{path.relative_to(ROOT)}: {exc}")
        continue
    for hit in UNTRUSTED.finditer(code):
        errors.append(
            f"{path.relative_to(ROOT)}:{code.count(chr(10), 0, hit.start()) + 1}: "
            f"local proof admission or axiom {hit.group(0)!r}"
        )
    local = []
    for name in IMPORT.findall(code):
        if name == "AllThoseRamseyClasses" or name.startswith("AllThoseRamseyClasses."):
            if name not in FILES:
                errors.append(f"{path.relative_to(ROOT)}: missing local import {name}")
            else:
                local.append(name)
    GRAPH[module] = local

colors = {}
stack = []


def visit(name: str):
    state = colors.get(name, 0)
    if state == 2:
        return
    if state == 1:
        errors.append("cyclic Lean import: " + " -> ".join(stack + [name]))
        return
    colors[name] = 1
    stack.append(name)
    for child in GRAPH.get(name, []):
        visit(child)
    stack.pop()
    colors[name] = 2


for module in GRAPH:
    visit(module)


def closure(name: str):
    reached, pending = set(), [name]
    while pending:
        current = pending.pop()
        if current in reached:
            continue
        reached.add(current)
        pending.extend(GRAPH.get(current, []))
    return reached


PUBLIC = "AllThoseRamseyClasses.PublicAPI"
APPLICATIONS = "AllThoseRamseyClasses.ApplicationsAPI"
POSET = "AllThoseRamseyClasses.Applications.PosetRamseyTheorem"
for name in (PUBLIC, APPLICATIONS, POSET, "AllThoseRamseyClasses"):
    if name not in FILES:
        errors.append(f"missing supported public module {name}")
if PUBLIC in GRAPH:
    polluted = sorted(x for x in closure(PUBLIC) if x.startswith("AllThoseRamseyClasses.Applications."))
    if polluted:
        errors.append(f"core PublicAPI imports application internals: {polluted}")
if APPLICATIONS in GRAPH and POSET not in closure(APPLICATIONS):
    errors.append("ApplicationsAPI fails to export the proved ordered-poset theorem")
if GRAPH.get("AllThoseRamseyClasses") != [APPLICATIONS]:
    errors.append("umbrella should import only ApplicationsAPI")

supported = closure(APPLICATIONS) if APPLICATIONS in GRAPH else set()
own_modules = {m for m in FILES if m.startswith("AllThoseRamseyClasses.")}
optional = sorted(own_modules - supported)
print(f"Local Lean modules (excluding CheckAxioms): {len(own_modules) + 1}")
print(f"Curated imports reach: {len(supported)} modules")
print(f"Optional directly importable research/audit modules: {len(optional)}")
print("Optional modules are compiled individually by CI; they are NOT assumed dead.")
print("Unreachable Published/* modules may document refutations or old proof routes.")

# Referee C: report real import redundancy before pruning declarations.
# Only local imports in the same direct import list are compared;
# external Mathlib/partite dependencies are left to the Lean build.
def redundant_direct(root: str) -> list[tuple[str, str]]:
    direct = GRAPH.get(root, [])
    return sorted((dep, through)
                  for dep in direct
                  for through in direct
                  if dep != through and dep in closure(through))


for root in (PUBLIC, APPLICATIONS, "AllThoseRamseyClasses", "CheckAxioms"):
    redundant = redundant_direct(root)
    print(f"Direct transitive-import redundancies in {root}: {len(redundant)}")
    for dep, through in redundant:
        print(f"  {dep} is already reached through {through}")

# Distinguish unused-by-curated-import from *not even* imported by
# the machine-checked theorem endpoint files. All Lean modules still
# receive a full kernel build; neither test is a licence to delete.
check_roots = sorted(m for m in FILES if m.startswith("CheckAxioms"))
axiom_reached: set[str] = set()
for m in check_roots:
    axiom_reached.update(closure(m))
not_in_axiom_roots = sorted(set(optional) - axiom_reached)
print(f"Modules outside curated API but covered by CheckAxioms roots: "
      f"{len(optional) - len(not_in_axiom_roots)}")
print(f"Optional modules not imported by CheckAxioms roots: "
      f"{len(not_in_axiom_roots)}")
for module in not_in_axiom_roots:
    print(f"  REVIEW (not proof of deadness): {module}")

# A module without incoming local imports is a separately compilable
# top-level leaf. This often means a publication counterexample,
# not throwaway code; its mathematical uses still need audit.
incoming = defaultdict(set)
for parent, children in GRAPH.items():
    for child in children:
        incoming[child].add(parent)
optional_roots = sorted(x for x in optional if not incoming[x])
print(f"Optional local-import roots: {len(optional_roots)}")
for module in optional_roots:
    print(f"  STANDALONE: {module}")

if errors:
    raise SystemExit("FAIL library audit:\n" + "\n".join(errors))
print("PASS import DAG, curated API surface, and admission/axiom source scan")
