# Track B: global selected-piece equality is exactly full-root all-test equality

**10 November 2026 — independent converse audit / new proof proposal.**
Original numbered 2019 manuscript remains frozen; do not restore author-removed
TODO notes.

## Mathematical statement

For any two genuinely **selected** finite forbidden geometric functional
rooted charts `P,Q` with the same width `n`, the following are equivalent:

* `Quotient.mk (globalFunctionalPieceSetoid F n) P = ... Q`: identical
  ORIGINAL globally indexed 2019 Myhill--Nerode equivalence class.
* Their ordered full native root structures on `Fin n` agree, and the
  corresponding rooted full-function extensions are equivalent against
  **every** forbidden full native free-amalgam test (with the second
  extension explicitly transported along root-structure equality).

The new Lean result is
`selectedFunctionalChart_global_class_eq_iff_rootEq_and_diagram`,
in `Lifts/GlobalProfileFromFullRootCongruence.lean`.

The reverse implication is the already validated
`selectedFunctionalChart_global_class_eq_of_rootEq_and_diagram`.
The genuinely new direction factors through three existing certified
ingredients:

1. `Quotient.exact` converts quotient equality to actual setoid equivalence;
2. `globalFunctionalPiece_equiv_root_eq` uses the REAL selected witness's
   incompatible complement to prove complete functional root-structure
   equality (not merely width or tuple equality);
3. `selectedGlobalPiece_to_fixedRoot`, followed by the canonical
   full-diagram/gluing equivalence, proves that all fixed-root tests agree.

The selected-piece hypothesis is **indispensable** for this conclusion as
stated: for arbitrary unselected charts, two distinct root structures with
empty incompatibility profiles can be globally equivalent. Neither
forbidden-class isomorphism closure nor a target weak-map injectivity
assumption is used.

## Consequence for Claim 2 formalization

The newly merged Track B/C same-Q source-step interfaces in PRs
[#979](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/979),
[#980](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/980),
and [#982](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/982)
return the original global piece symbol as well as an explicit full-root
all-test profile.

Because every state has a **genuine selected** geometric piece, this
bidirectional quotient theorem shows that, at a fixed positive width,
the profile condition is a logical consequence of global class equality.
The extra profile export is still valuable as a direct proof interface
and for contexts where a global selected quotient is not available.
One may now streamline the iterated state invariant by storing the
original global symbol, *without separately postulating ProfileFixed*.

**Important limitations:** This does not imply the outer ordered root's
TARGET image is injective (Track D), does not construct eligible inner
B-only flips from arbitrary positive-rank states, does not prove the
terminal A-only minimizer contradiction (Track C), and does not discharge
original shadow avoidance or unrestricted strong amalgamation.

## Validation

Do not declare this converse kernel-verified until its exact-head full
Lean CI, named `#print axioms`, permitted-axiom inventory, source-integrity
audit and no-admissions scan pass. The previous certified direction
is unchanged.

## Global-symbol and actual-source form (stacked companion)

The direct interface for the **original positive-width** lift symbol is
`selectedFunctionalChart_globalSymbol_eq_iff_rootEq_and_diagram` in
`Lifts/GlobalSelectedSymbolProfileEquivalence.lean`. It converts equality
of the two actual dependent `GlobalFunctionalPieceSymbol F` values into
equality of the selected quotient classes by the exact dependent-Sigma
pair injectivity theorem; the class iff above then yields the full root
and all tests. Conversely, equal full roots plus all tests yield the
exact SAME global symbol via the indexed-class congruence.

`geometricGlobalPieceSymbol_eq_iff_fullRoot_allTests` specializes
this to two genuine finite forbidden source geometric pieces of the SAME
ordered positive width. This is exactly the form returned by the
actual selected-Q Claim 2 flip endpoint. Thus when storing the original
global symbol across a sequence, `ProfileFixed` is *provably derivable*
at each genuine geometric state, not an extra mathematical invariant.

The theorem concerns **source charts**, not target weak-map images.
It neither enforces injectivity of the target outer-root tuple nor
constructs a positive-rank successor or terminal A-minimizer exit.
Named axiom checks and a protected root cover the new module.
Keep the companion PR draft until exact-head full CI is green.
