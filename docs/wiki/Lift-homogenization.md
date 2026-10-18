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


## Experimental folded-root alternative (distinct from the printed lift)

The printed canonical global relation requires an **injective image
of the ordered root tuple**, even when the realizing map is merely a
homomorphism-embedding. A weak HE can identify distinct vertices of
a reducible closed root. The explicit relational example and its
minimal-root collision are recorded in the
[separate manuscript proof audit](https://github.com/janhubicka/All-those-Ramsey-classes/blob/main/validation-lifts-weakimage-20261016.tex).

The **auxiliary folded global lift** retains the same genuine
global forbidden-piece class symbols and the same complete old
relations/functions, but allows a relation to be realized on
a tuple with repeated coordinates.

The following are separately Lean-certified and merged:

| Exact result | Lean source | CI / merge |
| --- | --- | --- |
| Folded global relation admits every weak selected-piece realization; yields a true equivalent replacement with the same complete functional root, even with colliding images | `Lifts/FoldedGlobalCanonicalRelations.lean` | [#399](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/399), [CI 38980171184](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38980171184), `88a60103` |
| An auxiliary folded relation builds a literal forbidden functional replacement-source diagram and weak compatible fold | `Lifts/FoldedGlobalDiagramFlip.lean` | clean [#407](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/407), [CI 38981225720](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38981225720), `52dc2efd` |
| Folded and printed canonical relations agree **exactly on injective tuples**, and positive folded relations are preserved under full old-language embeddings | `Lifts/FoldedGlobalRelationTransport.lean` | [#409](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/409), [CI 38981437427](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38981437427), `57e5553b` |
| Fixed finite functional shadows have finitely many expansions by any finite set of new relation symbols | `Lifts/FiniteFunctionalExpansionFibres.lean` | [#405](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/405), [CI 38980948053](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38980948053), `a156ce9d` |
| Regular piece quotient **plus a uniform root-width bound** yields finitely many total new global relation symbols | `Lifts/BoundedWidthGlobalPieceSymbols.lean` | [#406](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/406), [CI 38981164845](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38981164845), `06a23edf` |

The first two rows establish a genuine collision-tolerant
**witness-extraction and flip** mechanism for a different expansion.
They do not establish that two witnesses have a common full folded
lift or that their maximal folded expansions amalgamate.

The following exact statements are **CI-green on historical stacked
branches or being integrated on clean branches**, not yet all
promoted to the verified main-branch API:

- [#414](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/414)
  constructs relation agreement from a **common FULL folded lift**
  and performs the actual source flip. Its stacked proof in #401
  passed CI; clean integration must pass independently.
- [#403](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/403)
  combines the folded-common flip with strict A-only source support
  decrease. This remains **conditional** on the existence of the
  common full folded expansion and the relevant one-sided piece.
- [#410](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/410)
  derives a bound on genuine piece-symbol arities from a uniform
  bound on the sizes of forbidden source witnesses.
- [#413](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/413)
  assembles finite symbols and finite expansion fibres into a
  **bounded-width regular fixed-shadow precompactness** theorem.
- [#412](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/412)
  derives the needed common-root coordinate tuple from an actual
  selected source-piece map, with NO root-image injectivity.
- [#415](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/415)
  selects a one-sided genuine minimal-cut piece when the opposite
  exclusive source region occupies one Gaifman component. This
  explicit special-case hypothesis is NOT part of the general
  published theorem.

**Precompactness warning.** The finite-source/bounded-width
case is promising because finitely many global classes and a
uniform width bound give finitely many added symbols.
Regularity of an arbitrary infinite forbidden family does
not bound the widths. Repeated root coordinates may let
arbitrarily large-width folded relations appear on small
target carriers, so the printed distinct-root precompactness
argument cannot be reused without an additional theorem.

Even in the bounded-width case, the following remain open:
existence and maximality of the relevant common FULL folded
lifts, the multicomponent second minimality contradiction,
and the resulting full strong-amalgamation and Ramsey theorems.
This investigation is **not** a refutation of the published
theorem or a verified replacement for the original lift.

A standalone [author-review TeX note](https://github.com/janhubicka/All-those-Ramsey-classes/pull/122)
gives the precise folded-lift definition and conditional
English proof of the flip, with remaining obligations.


## 17 October: exact component structure and minimization

The folded-root auxiliary argument has progressed beyond the earlier
conditional diagram flip. The following endpoints are now **merged
and fully CI checked**:

| Result | Endpoint | Evidence |
| --- | --- | --- |
| Conditional collision-tolerant flip strictly decreases A-only **source** support, assuming a common full folded lift and the selected one-sided piece | `Lifts/FoldedCommonFlipStrictSupport.lean` | [#419](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/419), [CI 38985802308](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38985802308), merge `c7facb39` |
| In the **one-right-component** case, construct the minimal geometric piece, its positive-width full functional root, its left weak EHN factorization and the shared ordered root coordinates, then obtain strict support decrease with **no root-image injectivity** | `Lifts/FoldedSingleRightSupportDecrease.lean` | [#424](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/424), [CI 38986497427](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38986497427), merge `ddb189ee` |
| An opposite-side vertex found inside the selected piece cannot reconnect to the chosen opposite root after deleting the original root preimage; refactor the one-sided proof through this path lemma | `Lifts/MinimalGeometricCutComponentPath.lean` | [#423](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/423), [CI 38986175157](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38986175157), merge `8834bccf` |

The geometric content of the last item is precise: if
(Rsubseteq S=f^{-1}(X)) is the root of a genuine minimal piece
(P=Rcup C), selected by separating (xin F_A) from
(yin F_B), and (zin Ccap F_B), then **there is no path from
(y) to (z) avoiding (S)**. Thus a mixed piece must involve a
*different* right-exclusive component from the one selected as the
opposite root. This is the concrete obstruction that still requires
a multicomponent descent.

The following are **separate unmerged proofs or pending CI**; do not
confuse them with complete Claim 2:

- [#430](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/430)
  indexes exact source-minus-S components by a quotient of Gaifman
  reachability and certifies that a mixed piece meets two distinct
  right-exclusive component classes. Its historical stacked proof
  passed CI, but clean-main integration remains separately checked.
- [#428](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/428)
  derives the common full folded lift package from two full
  embeddings of the **same already supplied lifted expansion**,
  including exact old functional shadow maps. It does not construct
  maximal witness expansions.
- [#429](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/429)
  chooses a **finite** forbidden weak EHN witness with least
  A-only source support and proves the abstract strict-descent
  contradiction without any injectivization step.
- [#433](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/433)
  applies that minimization to the verified connected-right
  folded flip. Its one-component and shared-full-folded-lift
  assumptions remain explicit.

A separate [author-review draft](https://github.com/janhubicka/All-those-Ramsey-classes/pull/125)
gives a regular image-closed graph-family example with genuine
folded-root relation occurrences of unbounded arity on one
two-vertex shadow. It challenges an attempted reuse of the
**printed distinct-root counting argument**, but is not a proof
that the class of maximal folded lifts is non-precompact.
That example is currently an English adversarial audit, not Lean
certified.

**Still open:** the general multicomponent peeling/Claim 2,
existence of the relevant maximal folded lifts with sufficient
amalgamation, and the unrestricted Section 3 strong-amalgamation
and Ramsey consequences. The published 2019 theorem is not
claimed refuted or Lean certified by these conditional results.


## 17 October continuation: finite-family all-closed-component lift

The following is a **separate finite-forbidden-family construction**,
not a verification of the printed 2019 minimal-separator lift for
arbitrary regular infinite forbidden families. It names every genuine
`(function-closed source root, complementary source component)`
for each member of a *finite* list of *finite* forbidden native
functional structures. Its finite tag language records actual weak
EHN rooted realizations, even when distinct source-root vertices
have the same image.

The newest **merged, full-CI-checked** modules are:

| Milestone | Lean file | Verified PR |
| --- | --- | --- |
| Exact source-preserving component retargeting implies forbidden-source avoidance in a true full native functional free amalgam, assuming transfer of all closed-root component realizations | `Lifts/RootedTransferShadowAvoidance.lean` | [#459](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/459) |
| One common full finite-family canonical tag lift supplies that transfer for every named source; the free *shadow* is forbidden-free | `Lifts/FiniteFamilyShadowFreeAmalgamation.lean` | [#460](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/460) |
| Positive canonical tags are embedding-monotone; a maximal witness remains maximal under allowed extensions, and two maximal witnesses agree on the root **if an allowed common extension is already available** | `Lifts/FiniteFamilyCanonicalMaximality.lean` | [#461](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/461) |
| Maximal extension **exists** along any finite root by maximizing its finite set of positive canonical tag observations; `K` is a parameter and need not have AP or JEP | `Lifts/FiniteFamilyMaximalWitnessExistence.lean` | [#463](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/463) |
| The *actual full induced trace* of the canonical lift on the old root is constructed; its original partial functions remain exact, and equality of all canonical tag profiles constructs the common full tagged expansion needed above | `Lifts/FiniteFamilyCanonicalTrace.lean` | [#466](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/466) |
| Concrete strong amalgamation of two fully maximal canonical finite-family witnesses with matching full canonical tag profiles on a common root: the old free amalgam remains forbidden-free and the lifted embeddings reflect all tags with strong intersection | `Lifts/FiniteFamilyMaximalStrongAmalgamation.lean` | [#467](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/467) |

The maximum-profile proof uses a **finite observation space**, not
amalgamation or an assumed global maximal witness. In particular, the
arbitrary class predicate `K` in #463 must be specialized to the
**finite forbidden-free class** to guarantee a *finite* maximizing
witness. This finite specialization and preservation of maximality
under restriction to smaller FULL functional roots are proved in
[#468](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/468).

### 18 October: hereditary age and class-level strong amalgamation

The next steps are now **merged and fully CI checked**:

| Exact formal milestone | Proof module | PR |
| --- | --- | --- |
| Define finite maximal **induced** component-tag traces from finite forbidden-free ambient witnesses, maximal along the displayed root against finite allowed extensions; prove closure under arbitrary FULL expanded embeddings | `Lifts/FiniteFamilyMaximalTraceAge.lean` | [#476](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/476) |
| If one full old embedding is compatible with an allowed common witness, maximality transfers the original expanded structure as a FULL embedding into the actual trace on the larger root, with exact function fibres and reflection of all new tags | `Lifts/FiniteFamilyMaximalTraceTransfer.lean` | [#477](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/477) |
| The hereditary age of finite maximal traces has **strong amalgamation** over any arbitrary full expanded common root, using a genuine functional shadow free amalgam and a finite maximal extension along its carrier | `Lifts/FiniteFamilyMaximalTraceStrongAmalgamation.lean` | [#479](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/479) |

The class-level proof has a crucial asymmetry. Its objects are finite
expanded structures `X*` with an old shadow `X` embedded into some
**finite** forbidden-free `W`, where the new relation tables of
`X*` are the *FULL induced trace* of canonical relations of `W` and
`W` is maximal **along the image of X**. The witness need NOT be
maximal along its entire carrier. Canonical lifts themselves are not
claimed hereditary.

For strong AP, choose such witnesses `WA`, `WB` for two expanded
members `A*`, `B*`, together with full expanded embeddings of
their common `X*`. Reflection through these embeddings forces equal
**complete component-tag profiles** on the two copies of `X`.
The genuine OLD functional free amalgam `D=WA ⊕_X WB` excludes all
named forbidden weak EHN sources by the previously verified
source-preserving component retargeting/descent theorem (#460/#466).
Because `D` is finite and forbidden-free, take a finite forbidden-free
extension `M` maximal along `D` (#468). Its actual full induced
canonical trace on `D` belongs to the expanded age. The maximality
of `WA` along `A` and `WB` along `B` then supplies FULL
embeddings of the original expanded sides into this trace; the
underlying old pushout gives EXACTLY the desired intersection.

Thus this is a kernel-checked finite-family **heredity + strong AP**
theorem, not simply a conditional flip. The resulting expanded
amalgam need not be free in the added tag relations.

**Precompactness and expansion existence are now kernel verified.**
[PR #483](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/483)
(`Lifts/FiniteFamilyMaximalTracePrecompactness.lean`)
proves that for every finite native forbidden-free structure A,
the exact maximal induced-trace fibre over A is BOTH **nonempty
and finite**. Finiteness follows because the total family tag
language is finite and old relation/function tables are fixed;
nonemptiness follows from finite root-profile maximization (#468).

**Conditional JEP transfer is also kernel verified**:
[PR #482](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/482)
(`Lifts/FiniteFamilyMaximalTraceJEP.lean`) proves that the maximal
finite-family induced-trace age has FULL joint embedding whenever
the finite native forbidden-free class has FULL joint embedding.
The proof uses a finite native common witness, maximizes along its
root, and transfers both original expanded witnesses by FULL
embeddings. The premise is essential: disconnected forbidden
families and nullary functions must not be used to infer
unconditional JEP.

**The remaining principal targets** are the class-level Ramsey
property and a faithful repair/validation of the *printed* Section 3
minimal-separator lift for arbitrary connected, HE-image-closed,
regular infinite forbidden families. The all-closed-component
finite-family indexing used above does not yield the printed
regularity-based finite-arity-fibre/precompactness theorem for an
infinite family. In particular the original multicomponent Claim 2
and noninjective-root issues of `lem:amalgamationstr` are not
declared verified by these alternative finite-family results.

The numbered mathematical manuscript remains frozen; these
are library/wiki validation records only.
