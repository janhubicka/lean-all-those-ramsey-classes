#!/usr/bin/env python3
"""Review import-reachable proof modules and ongoing application roots.

Historical axiom-audit files do not serve as proof roots:
otherwise every abandoned experiment is falsely preserved.
The --plan option gives a deletion proposal; it NEVER deletes.
After approved pruning, --verify rejects remaining retired files.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import re

BASE = Path(__file__).resolve().parents[1]
paths = list((BASE / "AllThoseRamseyClasses").rglob("*.lean"))
paths += [BASE / "AllThoseRamseyClasses.lean"]
sources = {p.relative_to(BASE).with_suffix("").as_posix().replace("/", "."): p
           for p in paths}
checks = {p.stem: p for p in BASE.glob("CheckAxioms*.lean")}
rx = re.compile(r"(?m)^\s*import\s+([A-Za-z0-9_.]+)\s*$")
graph = {name: [dep for dep in rx.findall(path.read_text(encoding="utf-8"))
                if dep in sources] for name, path in sources.items()}

ACTIVE = {
    "AllThoseRamseyClasses",
    "AllThoseRamseyClasses.PublicAPI",
    "AllThoseRamseyClasses.ApplicationsAPI",
    "AllThoseRamseyClasses.Examples.MainTheorem",
    "AllThoseRamseyClasses.Examples.ClassApplicationBlueprint",
    "AllThoseRamseyClasses.Examples.OrderedPosets",
    "AllThoseRamseyClasses.Published.InducedClosed2019Lemma229",
    "AllThoseRamseyClasses.Applications.SteinerTripleClass",
    "AllThoseRamseyClasses.Applications.SteinerStrongEmbedding",
    "AllThoseRamseyClasses.Applications.SteinerTripleHereditary",
    "AllThoseRamseyClasses.Applications.SteinerTripleIsomorphism",
    "AllThoseRamseyClasses.Applications.SteinerAmbientRamsey",
    "AllThoseRamseyClasses.Applications.SteinerFreeAmalgamClosure",
    "AllThoseRamseyClasses.Applications.SteinerOrderPushout",
    "AllThoseRamseyClasses.Applications.SteinerStrongAmalgamation",
    "AllThoseRamseyClasses.Applications.SteinerLocalCompletion",
    "AllThoseRamseyClasses.Applications.MetricJumpSandwich",
    "AllThoseRamseyClasses.Applications.MetricJumpSamedist",
    "AllThoseRamseyClasses.Applications.MetricConvexityTransfer",
    "AllThoseRamseyClasses.Applications.MetricJumpQuotient",
    "AllThoseRamseyClasses.Applications.MetricBlockConvexity",
    "AllThoseRamseyClasses.Applications.MetricTwoPointClosure",
    "AllThoseRamseyClasses.Applications.MetricCanonicalQuotientMap",
    "AllThoseRamseyClasses.Applications.MetricCanonicalClosureFunctions",
    "AllThoseRamseyClasses.Applications.MetricPaperBlockSamedist",
    "AllThoseRamseyClasses.Applications.PaperOrderedGraphs",
    "AllThoseRamseyClasses.Applications.PaperForbiddenIrreducibles",
    "AllThoseRamseyClasses.Applications.PaperPointedEquivalences",
    "AllThoseRamseyClasses.Applications.PaperTotalUnaryFunctions",
    "AllThoseRamseyClasses.Applications.PaperAcyclicDigraphs",
    "AllThoseRamseyClasses.Applications.UnaryRootedClosureAudit",
}
missing = sorted(ACTIVE - sources.keys())
if missing:
    raise SystemExit("Missing active module: " + ", ".join(missing))
retained, todo = set(), list(ACTIVE)
while todo:
    current = todo.pop()
    if current in retained:
        continue
    retained.add(current)
    todo.extend(graph[current])
retired = sorted(set(sources) - retained)
kept_checks = set()
for name, path in checks.items():
    if name in {"CheckAxioms", "CheckAxiomsPublicAPI", "CheckAxiomsApplicationsAPI"}:
        kept_checks.add(name)
        continue
    imports = rx.findall(path.read_text(encoding="utf-8"))
    local = [dep for dep in imports if
             dep == "AllThoseRamseyClasses" or dep.startswith("AllThoseRamseyClasses.")]
    if not local or all(dep in retained for dep in local):
        kept_checks.add(name)
retired_checks = sorted(set(checks) - kept_checks)
parser = argparse.ArgumentParser()
parser.add_argument("--plan", action="store_true")
parser.add_argument("--verify", action="store_true")
args = parser.parse_args()
if args.plan or not args.verify:
    print(f"KEEP Lean modules: {len(retained)}")
    print(f"REMOVE retired Lean modules: {len(retired)}")
    print(f"KEEP axiom audits: {len(kept_checks)}")
    print(f"REMOVE stale axiom audits: {len(retired_checks)}")
    for name in retired:
        print("REMOVE_LEAN " + str(sources[name].relative_to(BASE)))
    for name in retired_checks:
        print("REMOVE_CHECK " + str(checks[name].relative_to(BASE)))
    for name in sorted(ACTIVE):
        print("PROTECTED " + name)
if args.verify:
    if retired or retired_checks:
        raise SystemExit("FAIL: retired modules or their axiom audits still remain")
    print("PASS: all Lean modules lie in the supported API or active application closure")
