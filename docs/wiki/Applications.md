# Ramsey-class applications: verified theorems and remaining cases

All unconditional statements below have compiled Lean proofs and permitted-axiom
audits. **Import `AllThoseRamseyClasses.ApplicationsAPI`** for the proved
applications; `PublicAPI` contains only the revised relational main theorem
and its foundations. Relational applications use full induced embeddings,
and functional applications use full function-preserving embeddings.

## Published 2019 examples: fully verified finite classes

| Original example | Lean theorem | CI certificate |
| --- | --- | --- |
| Freely ordered digraphs, including loops | `PaperGraphs.freelyOrderedDigraphs_areRamsey` | [PR #237](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/237) |
| Freely ordered simple undirected graphs | `PaperGraphs.freelyOrderedSimpleGraphs_areRamsey` | [PR #237](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/237) |
| Directed acyclic graphs with linear extensions | `PaperGraphs.freelyOrderedAcyclicDigraphs_areRamsey` | [PR #238](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/238) |
| Freely ordered `K_n`-free simple graphs | `PaperGraphs.freelyOrderedKnFreeGraphs_areRamsey` | [PR #241](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/241) |
| Finite ordered posets with chosen linear extensions | `OrderedPosets.orderedPoset_isRamsey` | [PR #227](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/227) |
| Freely ordered pointed equivalences | `PointedEquivalences.freelyOrderedPointedEquivalences_areRamsey` | [PR #239](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/239) |
| Finite B with any fixed finite number `m` of total unary functions | `TotalUnaryFunctions.freelyOrderedTotalUnaryFunctions_areRamsey` | [PR #240](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/240) |

The original paper uses a named reflexive order. The corresponding Lean
examples use a free, distinguished **strict** linear order. The graph and
acyclic examples are given as ordered relational structures with an
external order; functional embeddings reflect the **entire set of
function values**. These distinctions are explicit in the sources.

For the K_n-free case, the stronger reusable theorem
`ForbiddenPatterns.freeAmalgamation_of_irreducible_forbidden`
proves that forbidding an irreducible **full-embedding** pattern
preserves hereditary free amalgamation. The corresponding general
ordered Ramsey theorem is
`ForbiddenPatterns.orderedRamsey_avoiding_irreducible`.
This is proved for one forbidden pattern; do not silently present it
as a formalization of arbitrary infinite forbidden families.

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
These components remain direct imports, not purported complete metric
classes in `ApplicationsAPI`. Neither `prop:Smetric` nor the complete
metric Ramsey theorem is certified by the scalar reduction alone.

## Remaining manuscript applications

| Application | Verified ingredient | Unfinished obligation |
| --- | --- | --- |
| S-metric spaces without jumps | Numerical/completion components; rounded-sum/four-values algebra | Exact S-specific local completion and class Ramsey endpoint |
| Convexly ordered S-metrics with jumps | Abstract idempotent sandwich; finite scalar four-values reduction | Finite metric Ramsey proof, closure/local completion and convex-order transfer |
| Countably infinite target for m-unary operations | Finite-B Ramsey theorem, rooted-counterexample regression | Infinite Ramsey/quotient argument and countability statement |
| Multiple orders and interpositions | Proposed structural decomposition | Functional root representation and one fixed weak-test cutoff |
| Totally ordered incidence structures | Proposed incidence translation | Full embedding reflection, closed heredity, exact local completion |

The [working manuscript ledger](https://github.com/janhubicka/All-those-Ramsey-classes/blob/main/APPLICATIONS-VALIDATION-2026-10-14.md)
records earlier checks and TODOs; the manuscript's nonprinting
validation markers track later green finite applications.
