# All those Ramsey classes — the Lean research library

Mathematical documentation for Hubička–Nešetřil, *All those Ramsey classes*,
Advances in Mathematics 356 (2019), 106791.

The **coordinated corrected relational Theorem 2.18 is Lean-proved**,
including arbitrary fixed exact weak-test cutoffs. The literal 2019
formulation is refuted and must not be confused with the corrected one.
A genuine **finite ordered-poset Ramsey-class theorem** is now proved
in Lean as a completed application. The independent ordered
partial-function theorem 2.19 is in the pinned dependency.

| Chapter | Contents |
| --- | --- |
| [Using the library](Using-the-library.md) | Lake installation, imports, definitions and running examples |
| [Published statements](Published-statements.md) | Exact 2019 theorem scopes, corrections, proofs and unverified claims |
| [Proof architecture](Proof-architecture.md) | Generated closure profiles, strict-tree sparsening and fresh-tag pass |
| [Applications](Applications.md) | Proved posets; partial Steiner, metric and unary-function results |
| [Audit and validation](Audit-and-validation.md) | Theorem-level adversarial checks, source trust, unused-code criteria |
| [Publishing](Publishing.md) | Source-controlled wiki and automatic GitHub synchronization |

## Checked public endpoints

```lean
import AllThoseRamseyClasses
#check AllThoseRamseyClasses.Published.coordinated2019_theorem218
#check AllThoseRamseyClasses.Published.coordinated2019_ramsey_by_profile_sparsening
#check AllThoseRamseyClasses.Published.coordinated2019_profile_sparse_witness
#check AllThoseRamseyClasses.Applications.OrderedPosets.orderedPoset_isRamsey
#check StructuralRamsey.Structure.allThoseRamseyClasses_theorem_2_19_partialFunctions
```

Use `AllThoseRamseyClasses.PublicAPI` for the corrected relational core.
Use `AllThoseRamseyClasses.ApplicationsAPI` or the umbrella for completed
applications. The older proof and counterexample modules are separately
importable and compiled by CI, but are not implicit public dependencies.

**Essential semantics:** the repaired map and (4b) protect exact
induced structures that are BOTH intrinsically U-closed and
U-irreducible. Condition (4c) continues to test ALL original exact
weak induced subsets with at most n(B,C0) vertices, including
nonclosed subsets. The original ambient control C0 need not be closed.
No test may be silently replaced by its generated closure hull.

Evidence:
[general theorem PR #195](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/195),
[CI 38479503776](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38479503776);
[ordered-poset PR #227](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/227),
[CI 38633955517](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38633955517).

The canonical source of this wiki is the repository directory
[docs/wiki/](https://github.com/janhubicka/lean-all-those-ramsey-classes/tree/main/docs/wiki).
The [GitHub Wiki](https://github.com/janhubicka/lean-all-those-ramsey-classes/wiki)
was published successfully on 14 October 2026 from merged source
`e185d6105ac80643bf81b1cc3c4cbd8d11eee6c0` (workflow
[38642603486](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38642603486)),
and is automatically synchronized from subsequent source changes.
