#!/usr/bin/env python3
"""Adversarial SOURCE-CONTRACT regression checks for Section 3 lifts.

This deliberately does NOT certify the published lifting theorem. It checks
that documented CONDITIONAL Lean results retain the hypotheses on which their
mathematical statements depend. CI builds all modules and independently
checks named kernel axioms. Any theorem-strengthening must be accompanied by
a new proof audit and an intentional update to this file.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
LIFTS = ROOT / "AllThoseRamseyClasses" / "Lifts"

CONTRACTS = [
    ("OriginalClaim2InputCoveredOneStep",
     "exists_injectiveLeftMinimizer_and_strictRightReplacement",
     ("hImageClosed :", "hInputCover :", "hFree :", "hCommon :",
      "fullFreeRightExclusiveTarget")),
    ("EHNInjectiveSupportMinimizer",
     "exists_injectiveMinimalForbiddenEHNWitness_of_inputTests",
     ("hImageClosed :", "hCovered :")),
    ("FullFreeAmalgamOuterOldRootCriterion",
     "finite_outerOldRoot_hasGeometricPiece_of_oppositeBoundary",
     ("hPrivate :", "hExteriorBoundary :", "hInteriorBoundary :")),
    ("ActualNestedFunctionalProfileCongruence",
     "forbiddenNestedActualSource_iff_of_inner_profile_equiv",
     ("hIso :", "hOldMid :", "hNewMid :", "hExt :",
      "hOldOut :", "hNewOut :", "hOldT :", "hNewT :", "hEq :")),
    ("GlobalMaximalTraceConditionalStrongAmalgamation",
     "globalFiniteMaximalTraceAge_strongAmalgamation_of_shadowFree",
     ("hFreeK : GlobalCanonicalShadowFreeAmalgamation",)),
    ("GlobalShadowAvoidanceFromGeometricConditions",
     "globalCanonicalShadowFree_of_minimalGeometricConditions",
     ("hGeometry : GlobalMinimalWitnessGeometricConditions",)),
]

for module, theorem, tokens in CONTRACTS:
    path = LIFTS / (module + ".lean")
    source = path.read_text(encoding="utf-8")
    match = re.search(r"(?m)^theorem\s+" + re.escape(theorem) + r"\b", source)
    if match is None:
        raise SystemExit(f"MISSING lift theorem: {module}.{theorem}")
    end = source.find(":= by", match.end())
    if end < 0 or end - match.start() > 18000:
        raise SystemExit(f"Cannot isolate statement: {module}.{theorem}")
    signature = source[match.start():end]
    for token in tokens:
        if token not in signature:
            raise SystemExit(
                f"UNREVIEWED proof-contract change: {module}.{theorem} "
                f"lost {token!r}. Check manuscript TODOs before weakening "
                "the guard.")
    print(f"CONDITIONAL CONTRACT PRESENT: {module}.{theorem}")

print("PASS six lift theorem source contracts (NOT a proof of Section 3).")
