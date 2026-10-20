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

### 18 October continuation: exact reduct and regular isomorphism precompactness

**Exact finite-family reduct, fully Lean certified.**
[PR #491](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/491)
(`Lifts/FiniteFamilyMaximalTraceExactReduct.lean`, full
[Lean CI](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/39119057113))
shows that the underlying native functional shadow of EVERY member of the
hereditary finite-family maximal-trace age is forbidden-free. Conversely,
EVERY finite forbidden-free native shadow has a maximal-trace expansion.
Equivalently, its genuine maximal-trace expansion fibre is nonempty
**if and only if** the native structure avoids the finite named
weak-EHN forbidden family. This completes the exact-reduct direction
of the **finite-family alternative**, with all original function
value fibres preserved.

**Regular global canonical lifts: precompactness UP TO FULL ISOMORPHISM,
fully Lean certified.**
[PR #492](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/492)
(`Lifts/RegularLiftIsomorphismPrecompactness.lean`, full
[Lean CI](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/39119388795))
packages the previous finite-support and pullback transport results
into one explicit theorem. For an arbitrary **regular** family of
genuine forbidden-piece classes and any fixed finite old functional
shadow A, there is a finite collection of named-carrier expanded
representatives such that the original global **root-INJECTIVE**
canonical lift of ANY full-isomorphic old shadow is itself fully
isomorphic to one of these representatives. No uniform bound on
root width and no finite total lifted language is assumed; original
set-valued function data remain exact. This closes the counting /
isomorphism-type precompactness component of the printed construction,
**not** its maximal-witness strong-amalgamation or Ramsey conclusion.

The two developments deliberately remain separate: the finite-family
folded ALL-closed-component lift tolerates noninjective root-image
tuples and yields class-level strong amalgamation, while the original
regular global canonical lift uses only pairwise distinct root images
and now has full isomorphism-type precompactness. A regular infinite
family need not have finite active folded relation symbols on a fixed
finite carrier, so one cannot combine their advantages without an
additional argument.

**The remaining principal targets** are the Ramsey property of the
finite-family maximal-trace age, and a faithful proof or justified
repair of the printed Section 3 strong-amalgamation argument for
arbitrary connected, HE-image-closed, regular infinite forbidden
families. The original multicomponent Claim 2 and noninjective-root
issues of `lem:amalgamationstr` remain unresolved; neither #491
nor #492 claims that theorem.

The numbered mathematical manuscript remains frozen; these
are library/wiki validation records only.

## 19 October: actual regular global maximal-trace age and precise remaining gap

The **original distinct-root** regular infinite-family lift has now been
formalized beyond the counting theorem of 18 October. These are independent
full-CI-checked, merged results, not proposed proof sketches:

| Verified result | Lean source / pull request |
| --- | --- |
| Finite maximization produces a genuinely allowed maximal global canonical witness over every finite old root, using regularity and **no AP/JEP assumption** | `RegularGlobalMaximalWitnessExistence.lean`, [#494](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/494) |
| Exact **FULL induced** canonical global traces, preserving all old functions; restriction of maximality | `GlobalCanonicalInducedTrace.lean`, [#496](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/496) |
| Native forbidden-free EHN class is hereditary under full embeddings and invariant under full isomorphism | `GlobalForbiddenEHNAvoidance.lean`, [#498](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/498) |
| Hereditary age of genuine finite maximal global traces, with exact reduct over every finite allowed native structure | `GlobalMaximalTraceAge.lean`, [#500](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/500) |
| Actual FULL expanded embeddings of old maximal traces into compatible allowed extensions | `GlobalMaximalTraceTransfer.lean`, [#502](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/502) |
| The ENTIRE genuine maximal-trace expansion fibre over a fixed finite native structure is finite; for a hereditary allowed class K it is nonempty **iff** A belongs to K | `GlobalMaximalTraceExactFibre.lean`, [#501](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/501) |
| Full class-level strong amalgamation, constructing an actual finite maximal-trace amalgam with exactly prescribed overlap, **conditional on the explicit old shadow-avoidance principle** | `GlobalMaximalTraceConditionalStrongAmalgamation.lean`, [#503](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/503) |
| Full JEP of the maximal global trace age, **conditional on** native finite full JEP | `GlobalMaximalTraceJEP.lean`, [#504](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/504) |

### One unconditional subclass: irreducible forbidden sources

[PR #505](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/505)
proves unconditional native free-amalgam avoidance and hence original
global maximal-trace **strong amalgamation** whenever every forbidden
finite native source is irreducible. The EHN condition then embeds the
*whole* forbidden source FULLY into the amalgam; irreducibility
forces its image into one side, contrary to the side's avoidance.
No questionable weak-image injectivization is used.

[PR #506](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/506)
also proves the genuine **freely ordered Ramsey theorem** for the native
forbidden-free class in this irreducible-source case by applying the
previously verified all-arity EHN free-amalgamation Ramsey theorem.
This needs neither regularity nor an image-closed forbidden family.
It is a restricted **proved** Ramsey theorem, not the unresolved
general 2019 Section 3 theorem.

### Additional verified results and remaining general gap

The following 19 October milestones have since passed FULL Lean CI and
been merged:

* [#507](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/507):
  isomorphism-type precompactness of the **actual hereditary regular
  global maximal-trace age**, not just finite named-carrier fibres.
* [#508](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/508):
  full isomorphism-type precompactness of the finite-family folded
  maximal-trace age, allowing repeated root-image coordinates;
  exports generic full functional expansion pullback.
* [#509](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/509):
  an irreducible forbidden source has no genuine closed minimal
  separator piece; hence the entire added global piece-symbol type
  is empty for such forbidden families.

**The unrestricted reducible-source theorem remains OPEN.**
Its exact remaining class-level obligation is
`GlobalCanonicalShadowFreeAmalgamation F K`, with
`K=Forb_EHN(F)`: equal FULL root-injective global piece profiles
of two native forbidden-free witnesses must imply that their actual
native functional free amalgam is forbidden-free. The published
proof's tuple-surjective weak-image shortcut does NOT give an
injective witness in the same target. Root-image collisions and the
multicomponent Claim 2 flip remain unresolved, despite verified
precompactness and conditional global strong amalgamation.

The numbered 2019 mathematical manuscript remains frozen.

## 20 October: connected-source reductions without injectivization

These **merged, full-CI-verified** steps distinguish two independent
homogenizations and the exact source-root geometry:

| Result | Verification |
| --- | --- |
| Native full JEP of the original regular global maximal-trace age for finite connected nonempty forbidden sources over compatible FULL empty roots | [#511](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/511) |
| The previous common-empty-root condition is automatic when EVERY original relation and function symbol has positive arity | [#512](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/512) |
| The finite-family ALL-CLOSED-COMPONENT folded maximal-trace age has full JEP for connected forbidden sources with compatible empty roots, and without a separate root assumption for positive arity | [#517](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/517) |
| A connected nonempty weak EHN map into a FULL free amalgam which avoids its root factors through one full side; if both sides exclude the forbidden source, every obstruction must HIT the root | [#520](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/520) |
| The initial three-region partition of the printed proof is VALID without global map injectivity: both exclusive side regions and the shared-root preimage are nonempty; the latter is function-closed and separates opposite exclusive source vertices | [#523](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/523) |

Thus, for finite connected forbidden families in positive-arity native
languages, the folded maximal-trace age has the kernel-verified
**heredity, nonempty finite fibres, isomorphism-level precompactness,
strong amalgamation, and JEP** package. This is NOT yet its Ramsey
property. For the original infinite regular family, the proven JEP
does not imply the missing unconditional strong amalgamation.

### Additional merged source-root and Claim 1 results

The following have now also completed full Lean CI, were merged on
20 October, and keep the original native partial-function semantics:

* [#525](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/525):
  selects a genuine **positive-width** forbidden geometric piece from
  any connected source weak EHN obstruction crossing a full free amalgam
  of forbidden-free sides. The closed separator is a subset of the
  common-root PREIMAGE; only the SOURCE root enumeration is injective.
* [#529](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/529):
  packages the original quotient-indexed common-full-lift flip, forbidden
  replacement source, strict A-only SOURCE support decrease, and
  minimality contradiction, conditional on an actual one-sided piece
  and target **root-image injectivity**.
* [#527](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/527):
  extracts the common noninjective connected-source root-avoidance
  factorization, eliminating duplicate Gaifman-path arguments in the
  original-global and finite-family folded lift proofs while preserving
  their established theorem interfaces.

New dependent modules awaiting full independent CI and clean-main merge:

* [#530](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/530):
  the auxiliary *left piece weak EHN factorization* and *common-root
  coordinate tuple* required by #529 are consequences of genuine
  one-sidedness and shared-root containment; Claim 1 then forces the
  selected left component to meet the right-exclusive source region,
  **provided** its ordered target root images are injective.
* [#531](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/531):
  sufficient root-image injectivity when the whole induced function-closed
  root is IRREDUCIBLE (via EHN's full irreducible-test embedding), and
  the trivial width-one case; derive Claim 1 without an extra root
  injectivity premise for these strictly limited root configurations.

**Precise remaining gap:** even for a connected finite forbidden source,
the minimal function-closed separating root may be reducible and may
contain distinct source vertices that a weak HE identifies in the
target. The original distinct-root canonical lift does not record
such a noninjective tuple. The general selection of a one-sided
flippable piece or a sound root-image normalization, the genuinely
multicomponent Claim 2 argument, the unrestricted
`GlobalCanonicalShadowFreeAmalgamation` theorem for image-closed
regular families, and the final full Section 3 Ramsey lift theorem
remain OPEN. In particular no amount of finite-profile counting,
precompactness, or conditional strong amalgamation discharges
the missing shadow-avoidance lemma.

All additions remain in the version-controlled research wiki.
The original numbered mathematical manuscript is frozen.


## 20 October, later integration: original-global root collision audit

The pending labels on #530 and #531 in the earlier 20 October checkpoint
are superseded by subsequent successful main-branch merges. The source
of truth for these new results is the actual Lean theorem, not the
older provisional status in this chronology.

* [#530](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/530)
  now proves the one-sided Claim 1 reduction when the **target image
  of the selected root is injective**; its auxiliary EHN side map and
  shared-root coordinates are constructed from the geometric piece.
* [#531](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/531)
  and [#534](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/534)
  show that a residual one-sided obstruction must have width at least
  two, a reducible function-closed source root, and colliding target
  root images. These are necessary conditions, not existence.
* [#536](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/536)
  establishes the genuine support-minimal original-global dichotomy:
  either a selected positive-width geometric root has a collision in
  its target image, or its left component meets the opposite exclusive
  side. No global injectivization of the forbidden weak EHN witness.
* [#540](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/540)
  uses injectivity **only on the common-root preimage** to exclude
  the collision alternative and choose an actual mixed geometric piece
  minimizing the number of nonroot source vertices.
* [#544](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/544)
  further refines the collision alternative: if every pair of root
  vertices lies together in some FULL irreducible source test (possibly
  extending outside the closed root), the EHN map is injective on that
  root. Therefore a one-sided minimal obstruction cannot have such
  pairwise coverage, and the original dichotomy can be stated as
  **failure of source-side pairwise irreducible-test coverage or a
  genuine mixed piece**. This is now merged with full Lean CI.
* [#546](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/546)
  is **merged and full-CI verified**: with all right-exclusive source
  vertices connected outside the common-root preimage, the chosen
  piece cannot be mixed, so its root must fail pairwise irreducible-test
  coverage; coverage of the whole root preimage rules out that special
  obstruction. Its conclusion remains restricted to this case.

**Remaining gap unchanged.** Pairwise irreducible-test coverage and
single-component connectivity are NOT established for arbitrary
support-minimal forbidden weak witnesses. The truly multicomponent
proper-piece/flip descent of Claim 2, general
\`GlobalCanonicalShadowFreeAmalgamation\`, and the unrestricted regular
Section 3 Ramsey conclusion remain OPEN. The finite-family folded
construction's strong amalgamation and the irreducible-source Ramsey
special case are distinct already-verified results. No numbered
mathematical manuscript edits are authorized by these wiki records.


## Claim 2 audit after the original-global one-component reduction

The original printed Claim 2 (in \`ramsey.tex\`,
\`lem:amalgamationstr\`) is more than an assertion about disconnected
Gaifman components. It selects a smallest genuinely mixed piece
\`(P,R)\`, tries to flip proper sub-pieces of the opposite exclusive
colour, and uses neighbourhood closures to produce a **proper
sub-piece of the original forbidden source**. Source-map collisions
make the original root-injective piece predicates inapplicable to
some of these flips.

The next independently auditable certificates are:

* [#549](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/549)
  (**merged and fully CI-verified, #549**) packages an unconditional source-matched
  dichotomy at a minimum of actual left-exclusive source support:
  either a genuine closed separating root is **not** pairwise covered
  by irreducible full source tests, or two right-exclusive source
  vertices belong to different source-minus-common-root Gaifman
  components. The latter follows from the literal minimal-cut path
  obstruction, not from target injectivity. The theorem also selects
  a support-minimal witness from arbitrary witness existence.
* [#550](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/550)
  (**pending CI and merge**) proves the nested-cut set-theoretic
  descent for an actual mixed source piece: if \`R ⊆ S\`, the
  left component of \`F\\setminus S\` is a **proper subset** of the
  selected left component of \`F\\setminus R\`, and has strictly
  fewer vertices when \`F\` is finite. The proof uses genuine
  Gaifman reachability and the monochromatic source components
  outside \`S\`, with no image quotient.


* [#551](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/551)
  (**pending CI and merge**) isolates the EXACT two-sided
  boundary-closure implication used in the printed Claim 2.
  If \`C_x,C_y\` are components after deleting a larger cut \`R\`,
  and \`S ⊆ R\` is a smaller function-closed cut still separating
  them, then
  \`Cl(N(C_x)) ∩ Cl(N(C_y)) ⊆ S\`.
  This follows from the existing functional boundary-closure
  transport into the two disjoint components outside \`S\`.
  Consequently, any proposed old piece root contained in both
  boundary closures must lie in the new separating cut.

  **Not yet proved:** the old root of the minimal mixed piece
  actually lies in both boundary closures of the chosen source
  components, the premise needed to use this new theorem in the
  manuscript's \`R' ⊆ C\` argument.

**Crucial distinction:** the last proper inclusion does **not**
produce a proper *geometric forbidden sub-piece*. The full root
preimage \`S\` is closed but need not be an inclusion-minimal
separator, nor is \`S\` automatically contained in the original
selected piece \`P\`. To finish the printed Claim 2 one must
construct a genuine minimal function-closed root and a component
\`Q\` contained in \`P\`, preserve the exact source functional
structure, and prove that \`Q\` is either a smaller mixed forbidden
piece or can be flipped while preserving a forbidden EHN witness.
This final step must also handle possibly coinciding target images
of distinct root vertices. Neither #549 nor #550 asserts it.

The numbered manuscript and its editorially sensitive statements
remain frozen. These records track mathematical lemmas, not a
claim that Section 3 is fully verified.


## 20 October evening: localizing the genuine Claim 2 proper-subpiece step

The printed proof of \`lem:amalgamationstr\` uses a globally smallest
mixed *source-attached* piece \`P=R∪C\`. Its Claim 2 argument needs
two components \`A',B'\` of the original forbidden source outside
\`S=F_X\`, both lying in \`C\`, with the decisive inclusions

\`\`\`
R ⊆ Cl_F(N_F(A')) ∩ Cl_F(N_F(B')).
\`\`\`

These inclusions are **not** consequences of the already formalized
minimal-separator proposition by themselves: that proposition gives
boundary closure equalities for a pair of components after deleting
the *same minimal cut*. Here \`A',B'\` are components after deleting
the potentially larger, different cut \`S\`.

The following exact geometric statements are now **merged with full
Lean CI and axiom audits**:

* [#550](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/550):
  within an actual mixed piece, replacing the old root by the full
  common-root preimage strictly shrinks its selected component, in
  the SOURCE graph, and strictly lowers finite component cardinality
* [#551](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/551):
  every smaller function-closed cut separating components of a
  larger cut contains the intersection of their two generated
  neighbourhood closures
* [#552](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/552):
  assuming the two displayed boundary inclusions for chosen x,y,
  finite minimal-cut selection produces a GENUINE source-attached
  geometric piece with strictly larger root and strictly smaller
  selected nonroot component
* [#554](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/554):
  intersecting the larger source cut with the original geometric
  piece is function-closed and preserves EXACTLY the components of
  x,y in the original selected old component; the new cut separates
  them exactly as before

The following proofs are **pending full CI and integration**:

* [#555](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/555):
  a source-attached new geometric piece whose root stays inside
  the old piece, whose selected component is inside the old
  component and whose opposite distinguished vertex is inside the
  old component, is a literal **PROPER sub-piece** (including the
  entire new root), with strict total vertex count
* [#556](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/556):
  compose #552, #554 and #555 so the new root stays INSIDE the
  old piece. Under the same two boundary inclusions this produces
  an ACTUAL proper geometric sub-piece in the paper's sense, not
  merely a smaller abstract connected set
* [#559](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/559):
  under (i) injectivity of the original weak EHN source map on S
  and (ii) the exact two-boundary condition for a size-minimal
  mixed source piece, the new strict descent followed by verified
  Claim 1 produces a smaller genuine mixed piece, a contradiction
  to minimality; also gives a source intrinsic variant using
  pairwise full irreducible-test coverage of S

**Remaining major mathematical obligations.** The two displayed
boundary inclusions have NOT been established for the actual
unflippable \`B'\` and selected \`A'\` in the printed Claim 2.
Moreover weak EHN maps may identify root vertices, and the
original canonical lift records only distinct-root image tuples.
Even if the boundary argument is completed, either the
root-image normalization must be justified under the printed
image-closure hypothesis or the flip must be repaired to handle
collisions without destroying regular-infinite-family
precompactness. The unrestricted original-global strong
amalgamation and Ramsey theorems remain OPEN.

The numbered manuscript is frozen; this is only a validation
record, not an erratum or a claim of completed certification.
