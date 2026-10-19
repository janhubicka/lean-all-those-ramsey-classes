# Ramsey-class applications: verified theorems and remaining cases

All unconditional statements below have compiled Lean proofs and permitted-axiom
audits. **Import `AllThoseRamseyClasses.ApplicationsAPI`** for the proved
applications; `PublicAPI` contains only the revised relational main theorem
and its foundations. Relational applications use full induced embeddings,
and functional applications use full function-preserving embeddings.

## Shared application utilities

The pointed-equivalence and total-unary-function examples now reuse
[FunctionFibreUtilities.lean](../../AllThoseRamseyClasses/Applications/FunctionFibreUtilities.lean)
for singleton pullback/transport under **exact full fibre image equality**
and for the finiteness of a two-side-covered amalgam. Their original
researcher-facing declarations are unchanged; only their duplicate
proof bodies were replaced. The same utility also applies to arbitrary
function arities, so incidence-tag and closure-function proofs can
reuse it without assuming positive arity or global injectivity of
the function values. This does **not** replace the hypotheses required
to prove free amalgamation for a particular class.

## Published 2019 examples: fully verified finite classes

| Original example | Lean theorem | CI certificate |
| --- | --- | --- |
| Freely ordered digraphs, including loops | `PaperGraphs.freelyOrderedDigraphs_areRamsey` | [PR #237](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/237) |
| Freely ordered simple undirected graphs | `PaperGraphs.freelyOrderedSimpleGraphs_areRamsey` | [PR #237](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/237) |
| Directed acyclic graphs with linear extensions | `PaperGraphs.freelyOrderedAcyclicDigraphs_areRamsey` | [PR #238](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/238) |
| Freely ordered `K_n`-free simple graphs | `PaperGraphs.freelyOrderedKnFreeGraphs_areRamsey` | [PR #241](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/241) |
| Unrestricted digraphs omitting arbitrary families of tournaments as **positive copies** | `PaperGraphs.freelyOrderedPositiveTournamentFreeAllDigraphs_areRamsey` | [PR #361](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/361) |
| Oriented digraphs omitting arbitrary families of tournaments as **positive copies** | `PaperGraphs.freelyOrderedPositiveTournamentFreeDigraphs_areRamsey` | [PR #355](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/355) |
| Finite ordered posets with chosen linear extensions | `OrderedPosets.orderedPoset_isRamsey` | [PR #227](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/227) |
| Freely ordered pointed equivalences | `PointedEquivalences.freelyOrderedPointedEquivalences_areRamsey` | [PR #239](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/239) |
| Finite B with any fixed finite number `m` of total unary functions | `TotalUnaryFunctions.freelyOrderedTotalUnaryFunctions_areRamsey` | [PR #240](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/240) |

The original paper uses a named reflexive order. The corresponding Lean
examples use a free, distinguished **strict** linear order. The graph and
acyclic examples are given as ordered relational structures with an
external order; functional embeddings reflect the **entire set of
function values**. These distinctions are explicit in the sources.

For the K_n-free case, the reusable theorem
`ForbiddenPatterns.freeAmalgamation_of_irreducible_forbidden`
proves preservation of hereditary free amalgamation when one
irreducible **full-embedding** pattern is forbidden. PR #350 extends
this without a family-size bound: `ForbFamily` permits an arbitrary
indexed family of irreducible patterns with **varying carrier types**,
and `orderedRamsey_avoiding_irreducible_family` proves their
finite freely ordered Ramsey property.

The tournament remark has a nontrivial semantic distinction:
`freelyOrderedTournamentFreeDigraphs_areRamsey` excludes *full
induced* copies in unrestricted digraphs, while the Henson-style
`freelyOrderedPositiveTournamentFreeDigraphs_areRamsey` excludes
*positive directed subgraph* copies in loopless **oriented** graphs.
PR #355 proves these notions coincide in oriented targets (an
injective positive tournament copy must be induced), proves that
oriented graphs are a free-amalgamation class, and obtains the
unconditional Ramsey conclusion for any family of tournaments.
PR #361 supplies the stronger unrestricted-digraph theorem through
a general reduction of **positive** avoidance to **full induced**
avoidance of every same-carrier relational extension of the forbidden
pattern. These extensions stay irreducible, so the checked arbitrary
full-family theorem applies. Thus genuine positive tournament
subgraph avoidance is now certified even if the ambient digraph has
loops or opposite arcs. The class is distinct from the induced-copy
version; both use full embeddings for the actual Ramsey colourings.

## Ordered posets: exact weak local completion

```lean
import AllThoseRamseyClasses.ApplicationsAPI
open AllThoseRamseyClasses.Applications.OrderedPosets
#check orderedPoset_exactLocalAtControlCard
#check orderedPoset_isCoordinated2019Multiamalgamation
#check orderedPoset_isRamsey
```

The poset proof establishes actual strong amalgamation and exact weak
local completion at `n(B,C0)=|C0|` on **all original weak subsets**.
The ambient control need not already be closed. The finite poset
language has strict `.lt`, reflexive `.equiv`, and an inert empty
`.mate` predicate. [PR #227](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/227)
passed [CI 38633955517](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38633955517).

## Freely ordered partial Steiner triples: completed auxiliary example

**This is a separately added application, not an example in the
original 2019 paper.** The binary `covered` predicate marks an
increasing pair which has exactly one ternary `block` completion.
An unmarked pair is **not** a root. The class uses full
marked-pair strong embeddings rather than ordinary induced
hypergraph embeddings.

```lean
import AllThoseRamseyClasses.ApplicationsAPI
#check AllThoseRamseyClasses.Applications.SteinerTriples.orderedSteinerClass_strongAmalgamation
#check AllThoseRamseyClasses.Applications.SteinerTriples.orderedSteiner_exactLocal_zero
#check AllThoseRamseyClasses.Applications.SteinerTriples.orderedSteiner_isCoordinated2019Multiamalgamation
#check AllThoseRamseyClasses.Applications.SteinerTriples.orderedSteiner_isRamsey
```

The actual strong amalgam extends both old linear orders on the same
vertex pushout and preserves all marked-pair and block relations.
In the revised 2019 local axiom, every positive tuple's exact
U-closure hull is a closed U-irreducible K-test; its membership
permits completion of an arbitrary weak candidate using only a
compatible global order. **The local cutoff is zero**, and the
finite class is Ramsey. [PR #235](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/235)
and [PR #236](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/236)
passed the full Lean build and permitted-axiom audits; see the
[detailed proof note](../steiner-auxiliary-proof-20261015.md).

## Pointed equivalences and unary operations

Pointed equivalences are represented by finite sets with a **total
idempotent unary operation**, encoded as singleton-valued function
fibres. The Lean proof checks this equivalence, hereditary closure,
full functional free amalgamation and the unconditional ordered
Ramsey theorem. [PR #239](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/239).

For any fixed finite `m`, `TotalUnaryFunctions.totalUnaryClass_iff_functions`
identifies singletons in the set-valued functional language with
genuine total operations `Fin m → V → V`. The checked
`freelyOrderedTotalUnaryFunctions_areRamsey` proves the **finite-B**
part of manuscript `thm:unaryfunc`, with a finite target C.
[PR #240](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/240).
It **does not** certify the theorem's **countably infinite B** clause,
rooted-labelled closure quotient, or optional countability of C.

The separate Theorem 2.19 for genuinely partial single-valued
functions is exported from the pinned `partite-construction`
dependency as
`StructuralRamsey.Structure.allThoseRamseyClasses_theorem_2_19_partialFunctions`.

## Metric components, not yet a metric Ramsey application

`Applications.MetricFourValues` proves the scalar finite-distance
reduction `MetricSaturation.exists_finite_fourValues_extension`:
every finite D contained in a positive, well-defined four-values distance
set S has a finite four-values extension T contained in S, with its own
well-defined rounded sum. The proof includes actual capped-power
stabilization, finite generation in a commutative semigroup, exact
restricted-operation equality, and both directions of the four-values /
associativity bridge. Empty generators and empty S are allowed.

The reusable algebraic theorem `FiniteSemigroup.finite_closure` is about
Mathlib's actual generated subsemigroup, without an identity or a finite
ambient carrier. See [Metric applications](Metric-applications.md) and
[PR #244](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/244)
for the proof structure, exact assumptions and full CI review.
`MetricJumpThresholds` additionally proves the manuscript's gap/jump
criterion agrees with proper rounded-sum idempotence and compares ambient
jumps with those of a finite capped-closed subset. In
`MetricConvexityTransfer`, `exists_finite_fourValues_jumpConvex_extension`
combines finite four-values generation with invariance of the convexity
condition at jump distance thresholds, including the empty-distance case.
See [PR #245](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/245).
`MetricJumpSamedist` additionally specializes the idempotent sandwich
lemma to genuine S-metric distances and a neutral-zero operation on
S∪{0}. It proves constancy on threshold classes, on the paper's block
classes when their jump maxima are supplied, and positivity of the
constant for distinct classes. The separate
`MetricZeroExtension` proves the actual subtype operation laws.
See [PR #246](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/246)
and [Metric applications](Metric-applications.md) for exact hypotheses.
`MetricJumpQuotient` goes further: the threshold relation at every
proper jump or at zero is an equivalence relation, and the sandwiched
cross-distance descends to an **exact quotient-invariant label** for
pairs of classes. This is not yet a metric on imaginary vertices:
the diagonal and inter-level distance construction remain separate.
See [PR #247](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/247).
**PR #248 now closes the finite block gap**: `MetricFiniteBlocks` and
`MetricFiniteBlockMaximal` prove that maximal no-jump four-values blocks
of finite S are precisely the jump-cut signature pieces, and every
non-top block ends at an ambient jump. `MetricPaperBlockSamedist`
derives the block maxima and the existence/uniqueness of a block at each
proper jump; `finite_paperBlock_samedist_published` proves the corrected
finite-S lemma under the original gap-jump and disjoint-class assumptions.
`wellDefined_of_finite` removes the unnecessary extra well-definedness
premise. See [Metric applications](Metric-applications.md) and
[PR #248](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/248).
**PR #249 verifies the finite convex-order interface.** The theorem
`paperBlockConvex_iff_jumpConvex` identifies the paper's block-convex
metric orders with the already formalized jump-threshold convexity.
`paperBlockConvex_iff_capped_subset` proves exact preservation of the
paper's block-convexity when passing from finite S to a finite
capped-closed T⊆S for a T-valued metric, deriving four-values for T.
See [PR #249](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/249).
The neutral-zero convention is essential and must be stated explicitly
in a corrected manuscript; the printed four-point proof remains invalid
at zero. These modules are directly importable components, not complete
metric Ramsey classes in `ApplicationsAPI`. The full class-level Ramsey
theorem and the general infinite-S block interpretation remain open.

## One-point metric closure: a checked construction component

`Applications.MetricOnePointClosure` now proves the actual
S-metric extension obtained by adjoining a single positive-jump
closure vertex at a chosen root. Original distances are unchanged;
the new vertex is at distance exactly j to every member of the
root's j-class and at distance ≤j to no other original vertices.
The formula `j⊕d(root,x)` is independent of which class member
is used for the two-edge attachment path, and is maximal among
S-metric extensions with that root edge. Full CI and axiom audit:
[PR #250](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/250),
[CI 38761542466](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38761542466).

This is a genuine metric construction, not the paper's entire
lift `L(A)`: all tagged jump-class imaginaries, their inter-level
distances, the extended order and embedding extension are still
open. See [Metric applications](Metric-applications.md) for
the proof and exact source endpoints.

## Two-closure metric cross distances

`Applications.MetricTwoPointClosure` composes two verified one-point
metric adjunctions and proves the new inter-closure distance is
`j⊕d(r,s)⊕k`, exactly the quotient-invariant class-pair label.
The result is an S-metric, preserves the original distances and
is independent of which closure vertex was attached first.
See [PR #251](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/251),
[CI 38763120354](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38763120354)
and [Metric applications](Metric-applications.md) for exact proof scope.
Distinct attached tags are not yet automatically deduplicated by
their block class; the full L(A) lift remains unfinished.

## Finite towers: every closure-pair distance

`Applications.MetricClosureTowerLabels` extends the checked finite
metric tower to indexed closure stages and proves the universal
pairwise formula
`d(v_i,v_k)=j_i⊕d(r_i,r_k)⊕j_k` for any distinct stages.
Each closure-to-original distance is likewise independent of later
attachments. This supplies the complete distance matrix on the
formally tagged finite tower and agrees with the quotient sandwich
label, but does **not** yet identify duplicate tags or construct
the canonical `L(A)`. See
[PR #253](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/253)
and [Metric applications](Metric-applications.md).

## Directly tagged finite closure metric

`Applications.MetricTaggedClosure` supplies an actual finite
S-metric on `V ⊕ Fin n`, with all original distances unchanged,
closure-to-original distances `j_i⊕d(r_i,x)`, and distinct
closure-to-closure distances `j_i⊕d(r_i,r_k)⊕j_k`.
It proves off-diagonal membership in the positive distance set,
not merely a pullback pseudometric. See
[PR #254](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/254)
and [CI 38774053990](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38774053990).
Choosing canonical unique (jump,class) tags, the lifted
order and functorial embeddings remain separate.

## Canonical metric on unique jump-class imaginaries

The finite metric carrier is no longer based on arbitrary attachment
stages. `Applications.MetricCanonicalJumpTags` defines one tag for
each dependent pair (proper jump, original threshold-equivalence class),
with a proved finite enumeration. `MetricCanonicalFiniteLift`
constructs a genuine S-metric on precisely that carrier.
`Applications.MetricCanonicalDistance` then defines the distance
**explicitly**, with zero diagonal and representative-invariant
sandwich formulas for all other pairs. It proves the resulting
`canonicalDistance` is a genuine S-metric, including the empty
original-space case.

See [Metric applications](Metric-applications.md), Lean
[PR #255](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/255),
[PR #257](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/257),
[PR #258](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/258),
and full [CI 38779692029](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38779692029).

The complete finite canonical `L(A)` embedding-map components
have since been certified: convexity, all original/new closure
order comparisons, exact preservation of the completed partial
function table and uniqueness are collected in
`MetricSaturation.canonicalLift_finite_orderedFunctionalEmbedding`
and `mapCanonicalLift_unique_of_completedClosure`,
[PR #342](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/342).
The numbered lemma also has an infinite-S formulation and needs an
exact source-matching bridge. Finite metric Ramsey, class-level
strong amalgamation and exact local completion remain open.

## Isometry-induced maps on canonical closure tags

The reusable `MetricCanonicalQuotientMap` component transports
original jump-equivalence classes along an exact metric isometry.
It proves the quotient map is injective and the dependent
canonical-tag map preserves the jump level and representative
class. See [PR #260](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/260)
and the [metric API note](Metric-applications.md). Full
canonical **metric** isometry on lifted vertices still needs
the cross-distance/representative-independence bridge and
injectivity of the dependent tag map; the convex order and
Ramsey class are not implied.

## Canonical labels independent of chosen class roots

`Applications.MetricCanonicalLabelInvariance` now certifies
the exact quotient-label identities for mixed and
distinct closure-pair distances. The formulas in
`canonicalDistance` may use **any** original roots
representing the same jump classes, not only the
implementation's `Quotient.out` representatives.
This is a reusable prerequisite for functorial metric
embeddings of the lifted structures.
See [PR #261](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/261),
[CI 38798821065](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38798821065)
and [Metric applications](Metric-applications.md).

The canonical **metric embedding** is verified by
`MetricCanonicalLiftEmbedding.mapCanonicalLift_isometry`
and `mapCanonicalLift_injective`, [PR #274](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/274).
The exact lifted **order preservation**, including closure-to-closure
comparisons, is now proved in [PR #336](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/336).
The assembled metric, order and completed partial-function
embedding certificate is [PR #342](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/342).
These proofs do not imply class-level metric Ramsey without the
remaining functional amalgamation and local-completion arguments.

## Nested metric closure functions and canonical insertion order

`Applications.MetricCompletedClosureFunctions` checks the
completed F_j table on all originals and lower-jump closure
vertices, including the newly assigned edges of distance
exactly j. [PR #273](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/273),
[CI 38813295544](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38813295544).

`Applications.MetricCanonicalInsertionOrder` constructs
the faithful linear order via (last original class member,
jump level), using a bottom value to keep originals
before their attached closures. The order extends
the originals and sorts nested levels increasingly.
[PR #270](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/270),
[CI 38824390934](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38824390934).

The completed canonical order is now checked through the
nested class-interval convexity and full old/new order transport;
[PR #293](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/293)
checks the manuscript's literal paper-block convexity, and
[PR #336](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/336)
checks all pairwise order comparisons. The combined embedding
certificate is PR #342. Full functional strong amalgamation,
exact weak local completion and the finite metric Ramsey
theorem remain open; do not mistake the embedding certificate
for a class-level Ramsey proof.

## Newly completed forbidden-pattern and admissible-order examples

The general **positive-copy avoidance** theorem is now proved for an
arbitrary family of irreducible relational patterns. Positive
embeddings need only preserve relation tuples, but are injective;
Ramsey copies remain *full/induced* embeddings. By passing to all
same-carrier relational extensions of the forbidden patterns, this
reduces to the checked full-forbidden-family criterion. In particular,
`PaperGraphs.freelyOrderedPositiveTournamentFreeAllDigraphs_areRamsey`
covers unrestricted finite digraphs allowing loops and digons;
[PR #361](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/361).
This generalizes the oriented positive-tournament theorem, PR #355,
without conflating positive and induced tournament copies.

The loop-first admissible-order Ramsey example is fully proved:
`PaperGraphs.loopFirstOrderedDigraphs_areRamsey`,
[PR #358](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/358).
The target order is obtained by sorting looped vertices first and
preserving the original order within each one-point type. The
old witness is **not** globally order-embedded in the reordered
witness; the proof uses B-copywise Ramsey transfer.

The arbitrary **relational one-point-type** version is now fully
checked: `AdmissibleOrders.typeAdmissible_arrow_of_freeOrder`,
[PR #367](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/367),
proves copywise Ramsey-arrow transfer for any relational reduct
class whose freely ordered Ramsey witnesses are available.
The type record is packaged as a new `OnePointCode` carrier,
so a chosen *total* order of one-point types is not confused with
the inclusion order on sets.

Moreover, `AdmissibleOrders.admissiblyOrderedFreeAmalgamation_areRamsey`,
[PR #372](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/372),
proves the full finite Ramsey-class conclusion for any relational
free-amalgamation class equipped with these admissible orders.
The unrestricted arbitrary-relational-class theorem is now
fully verified by [PR #373](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/373):
`AdmissibleOrders.hasTypeAdmissibleRamsey_of_hasFreeOrderRamsey`
asserts the implication between genuinely class-level Ramsey properties,
with NO free-amalgamation hypothesis. genuine function-language one-point
types and the manuscript's named reflexive-order representation
remain separate from the verified relational results.

## Totally ordered relation instances: paper Theorem TO

The source-matched `thm:TO` formalization is packaged as
`TotallyOrderedIncidence.genuinelyTotallyOrderedRelations_areRamsey_finiteSignature`
in `TotallyOrderedRelationsFiniteSignature.lean`.
**Fully verified and exported in `ApplicationsAPI`**: the genuine
source/target construction and full Ramsey arrow passed the complete
Lean build, axiom and admission scans in
[PR #499](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/499)
(merge `ab8ca7d3`); the removal of the auxiliary symbol-order
assumption passed independent CI in
[PR #513](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/513)
(merge `de376fae`); and the exported API passed full CI in
[PR #514](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/514)
(merge `843deb68`).

Objects consist of a finite relational structure with a genuine linear
vertex order and, **separately for each relation symbol**, a genuine
linear order of the POSITIVE instances of that relation. Negative tuples
are not spuriously ordered. The proof works for arbitrary finite
relation arities, including zero, and does not require a preselected
linear order on the finite type of relation symbols.

The 2019 doubled-arity encoding preserves and reflects full embeddings.
A canonical incidence expansion attaches a function-output tag to each
positive relation instance; its external order puts original vertices
first, then tags by symbol and the source tuple order. The actual EHN
Ramsey step is run in a larger **orphan-tolerant** class of marked
functional structures, which is free-amalgamation closed and does
not require any INTERNAL target order to be linear. An arbitrary
weak Ramsey witness is decoded on its Old-marked vertices. Positive
tuple orders in the decoded target compare the singleton output tag
first, and the entire original input tuple second to resolve
collisions. Every selected full auxiliary copy of a canonical
source projects to an honest original copy; the generic copywise
Ramsey arrow transfer finishes the proof.

The final result asserts a Ramsey arrow into an **actual**
`OrderedRelations` target and a finite original vertex type.
It is distinct from the older
`totallyOrderedRelations_arrow_of_canonical_orders` conditional
interface, which assumes compatible source incidence orders and
returns an unconstrained `TotalOrderData` record.
The old partial/set-valued function output fibres are compared
exactly, not merely by forward preservation.

## Remaining manuscript applications

| Application | Verified ingredient | Unfinished obligation |
| --- | --- | --- |
| S-metric spaces without jumps | Numerical/completion components; rounded-sum/four-values algebra | Exact S-specific local completion and class Ramsey endpoint |
| Convexly ordered S-metrics with jumps | Fully audited finite canonical metric/order/partial-function embedding certificate (PRs #336, #342), paper-block convexity (#293), proper-jump crossing and empty-base metric gluing (#346, #349) | Complete nonempty-base functional strong amalgamation, simultaneous nested order extension, corrected weak local completion and the finite class Ramsey theorem |
| Countably infinite target for m-unary operations | Finite-B Ramsey theorem, rooted-counterexample regression | Infinite Ramsey/quotient argument and countability statement |
| Multiple orders and interpositions | Proposed structural decomposition | Functional root representation and one fixed weak-test cutoff |

The [working manuscript ledger](https://github.com/janhubicka/All-those-Ramsey-classes/blob/main/APPLICATIONS-VALIDATION-2026-10-14.md)
records earlier checks and TODOs; the manuscript's nonprinting
validation markers track later green finite applications.
