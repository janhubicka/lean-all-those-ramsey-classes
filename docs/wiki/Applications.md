# Ramsey-class examples: proved results and open applications

A class-level Ramsey statement is certified only when there is an
unconditional Lean declaration of type `FiniteRamseyClass K`.
A compiled partial construction or conditional class blueprint
does not suffice.

## Fully verified finite ordered posets

```lean
import AllThoseRamseyClasses.ApplicationsAPI
open AllThoseRamseyClasses.Applications.OrderedPosets
#check orderedPosetClass
#check orderedPoset_exactLocalAtControlCard
#check orderedPoset_isCoordinated2019Multiamalgamation
#check orderedPoset_isRamsey
```

The proof establishes strong amalgamation, closed heredity,
isomorphism invariance, the ordered ambient Ramsey property,
quasi-cycle exclusion and exact weak local completion for the
preselected cutoff n(B,C0)=|C0|. The weak source is not assumed
itself already ordered or a poset. The completed target retains
the same carrier and reflects all original full B-copies.
The Lean language uses strict vertex order `.lt`,
reflexive partial-order relation `.equiv` and an inert empty
`.mate` relation. It describes finite posets with chosen linear
extension after forgetting the empty relation and translating
strict/reflexive order.

Certificate: [PR #227](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/227);
[full CI 38633955517](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38633955517).

## Verified independent ordered partial-functions theorem

The pinned `partite-construction` dependency exports
`StructuralRamsey.Structure.allThoseRamseyClasses_theorem_2_19_partialFunctions`
for finite genuinely partial **single-valued** functions and full
functional embeddings. This is not the manuscript's arbitrary
countable-target total-unary-function theorem.

## Partial: freely ordered partial Steiner triples

The concrete marked-pair language has binary `covered` root
markers and ternary `block` outputs, plus an arbitrary linear
vertex order. The closure rule is on an **increasing marked pair**,
not on all pairs.

Proved components:
* `SteinerTripleClass` / `SteinerTripleHereditary` /
  `SteinerTripleIsomorphism`: encoding, intrinsic closedness,
  hereditary and isomorphism laws;
* `SteinerAmbientRamsey`: mixed-arity ambient Ramsey theorem;
* `SteinerFreeAmalgamClosure`: unique block extension over
  marked roots survives genuine strong-root free amalgamation,
  PR [#228](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/228),
  successful CI [38634510358](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38634510358);
* `SteinerOrderPushout`: compatible arbitrary vertex order
  on the actual free-amalgam carrier, PR
  [#229](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/229),
  successful CI [38634438870](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38634438870).

**Still open**: full block/covered-pair normal-form laws and
reflection on both amalgam sides, a complete strong-amalgamation
class theorem, exact original weak local completion, and hence
the unrestricted partial-Steiner K-Ramsey conclusion.
Do not infer the class theorem just from the two amalgamation pieces.

## Other original paper examples

| Application | Current validation | Remaining work |
| --- | --- | --- |
| S-metrics without jumps | numerical and completion components | edge cases, true S-specific local completion and class instance |
| Convex S-metrics with jumps | abstract idempotent sandwich | finite-generator closure and complete metric class interface |
| Pointed equivalences | generic closure infrastructure | exact weak-source locally finite completion |
| Total unary functions, countable targets | separate partial-functions theorem, rooted counterexample | correct rooted quotient, convex types and countable result |
| Free interpositions/permutations | class proof strategy | two inverse closures, common fixed weak-test cutoff |
| Ordered incidence structures | relational model | embedding reflection, closed heredity, local completion |

The [manuscript application ledger](https://github.com/janhubicka/All-those-Ramsey-classes/blob/main/APPLICATIONS-VALIDATION-2026-10-14.md)
tracks exact source statements, corrections and open obligations.
