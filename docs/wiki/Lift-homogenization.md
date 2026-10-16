# Section 3: forbidden-piece lifts and strong amalgamation

This page tracks the **independent** formalization of the paper's
Section 3 homogenizing lifts. It is distinct from the already verified
corrected relational multiamalgamation theorem (Theorem 2.18), and
the full Section 3 strong-amalgamation theorem is **not yet proved**.

The maintained Lean code is in
[`AllThoseRamseyClasses/Lifts/`](../../AllThoseRamseyClasses/Lifts/).
Each certified module has an individual `CheckAxioms*.lean` endpoint
and a reachable active root. The latest public API does not yet export
an unrestricted Section 3 class theorem.

## Verified structural checkpoints

| Paper step | Compiled proof endpoint / relevant files | Validation evidence |
| --- | --- | --- |
| Partial-function semantics and weak quotient | `OriginalPartialWeakImageQuotient.lean`: original partial HE and tuple-surjective generated quotient | [PR #384](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/384), [CI 38963897106](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38963897106) |
| Actual functional piece geometry and full root charts | `GeometricFunctionalPieces.lean`, `GeometricPieceRootChart.lean`, `GeometricGlobalFreeDiagram.lean` | merged modules, individual axiom audits |
| Global quotient-indexed piece relations and canonical lift | `GlobalFunctionalPieceLift.lean`, `GlobalPieceFixedRootBridge.lean`, `GlobalCanonicalFixedRootWitness.lean` | merged modules, individual axiom audits |
| Common full global lift and conditional flip | `CommonFullGlobalPieceFlip.lean`, `GlobalSharedPieceFlip.lean` | merged modules, individual axiom audits |
| Exact finite support conservation and strict decrease after flips | `FlipExclusiveSupport.lean`, `FlipSupportStrictDecrease.lean`, `GeometricFlipSupportDecrease.lean` | [PR #381](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/381) and [PR #387](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/387) |
| Weak source partitions, Gaifman edges, and root separation | `WeakSourceFreeAmalgamPartition.lean`, `WeakFunctionalGaifmanProjection.lean`, `WeakFreeGaifmanComponents.lean` | [PR #392](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/392), [CI 38971096046](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38971096046) |
| Existence of an inclusion-minimal **closed** cut inside a finite closed separator | `FiniteClosedSeparatorSelection.lean` | [PR #393](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/393), [CI 38971926494](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38971926494) |
| Actual forbidden geometric piece from a weak source cut | `WeakMinimalGeometricChart.lean` | [PR #394](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/394), [CI 38973945484](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38973945484) |
| Piece side dichotomy and full EHN side factorization | `GeometricPieceSideDichotomy.lean` | [PR #395](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/395), [CI 38974283786](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38974283786) |

Use exact module imports for experimental reusable lemmas, e.g.:

```lean
import AllThoseRamseyClasses.Lifts.WeakMinimalGeometricChart
import AllThoseRamseyClasses.Lifts.GeometricPieceSideDichotomy

#check AllThoseRamseyClasses.Lifts.weakFreePartition_hasForbiddenGeometricPiece
#check AllThoseRamseyClasses.Lifts.weakGeometricPiece_left_or_component_meets_right
#check AllThoseRamseyClasses.Lifts.weakGeometricPiece_factor_left_if_no_right
```

## Verified geometry, stated accurately

Let `f : F → D` be a weak EHN homomorphism-embedding into a genuine
functional free amalgam `D=A ⊕_X B`. The inverse image
`F_X=f⁻¹(X)` is function-closed. Source vertices mapped to the
two opposite exclusive sides cannot be linked by a Gaifman path
avoiding `F_X`, regardless of collisions of `f`.

For any selected left- and right-exclusive source vertices, finite
minimal-cut selection finds `R ⊆ F_X` which is inclusion-minimal
among **function-closed** separators of those vertices. Its entire
source vertex set can be enumerated without repetitions by
`Fin n`; the resulting chart is an **actual** geometric forbidden
piece, not an arbitrary rooted candidate. The native induced
function fibres and old relations are retained.

For any genuine geometric piece whose roots lie in `F_X`,
either its entire vertex image is contained in `A`, or its selected
component contains a right-exclusive vertex. In the first case
the piece's weak HE genuinely factors through the full embedding
`A ↪ D`.

These facts do **not** imply that `f` is injective on the piece's
ordered roots. Source-root distinctness is not target-image
distinctness. Nor do they imply that a selected piece automatically
avoids the opposite exclusive side.

## Additional verified conditional theorems

- [PR #396](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/396),
  [CI 38975142048](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38975142048),
  merged `cfca141ba624`: the actual common-global-lift forbidden-source
  flip, together with the strict support inequality, constructs a new
  forbidden weak-HE witness with fewer **A-only source vertices**.
  Hypotheses explicitly include a common **full** canonical lift,
  compatible piece/root maps, injectivity of the selected root **image**,
  finite forbidden source and replacement source, and a chosen
  A-only vertex of the selected component. Global map injectivity
  is not required. This is a **conditional Claim 1**, not the
  unrestricted paper claim.
- [PR #397](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/397),
  [CI 38975309197](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38975309197),
  merged `e59d259eb13d`: an actual Gaifman path between selected
  vertices in the original source rules out an empty separating cut,
  yielding positive root width. This is the precise path-based bridge
  to positive-width global lift symbols; connected forbidden sources
  must supply that path in any eventual unrestricted theorem.

These are **Lean-verified under their displayed hypotheses**.
Neither supplies the missing root-image injectivity nor completes
the strong-amalgamation theorem.

## Proof gap that must not be hidden

The original manuscript states that the forbidden-family
tuple-surjective HE-image closure permits choosing an *injective*
forbidden homomorphism-embedding into the **same target**.
This implication fails without further hypotheses.

The generated quotient `F → Q` is a tuple-surjective original
partial-function HE, but the inclusion `Q → D` can preserve
positive incidences without being a full homomorphism-embedding.
A small relational example with forbidden family
`{C₅, K₃}` (empty ternary relation) and a triangle target
with an additional ternary tuple also exhibits a genuinely
minimal separating root with colliding images. See the separate
[manuscript review-only audit](https://github.com/janhubicka/All-those-Ramsey-classes/blob/main/validation-lifts-weakimage-20261016.tex).
Those finite examples currently have detailed English audits,
not Lean counterexample certificates. They concern the invalid
proof shortcut, **not** a refutation of the main theorem.

A repair must either derive suitable root-image injectivity from
the **actual maximal-witness/free-amalgam configuration**, or develop
a replacement flip/lift mechanism which tolerates collapsed roots.
An unrestricted Claim 1, Claim 2, `lem:amalgamationstr` and the
full Section 3 strong-amalgamation theorem remain **open**.
