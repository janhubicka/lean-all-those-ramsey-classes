# Track C: exact native free decomposition of uncovered function/relation input tuples

16 November 2026. Independent add-only module, no change to frozen
numbered 2019 manuscript.

The current conditional original 2019 Claim 2 normalization reduces
the first-state obstruction to source-local FULL irreducible function
input tests and positive relation-tuple preimages.

Here failure of either is converted into an ACTUAL native geometric
certificate, not just an opaque missing hypothesis.

- An uncovered original primitive function-input tuple has a
  FUNCTION-CLOSED generated native source hull that is reducible.
  A genuine proper FULL free decomposition of that hull exists,
  with the original generators crossing BOTH sides.
- An original weak EHN map whose target-image OLD positive
  relation tuple has NO positive source tuple preimage has a
  chosen actual original source tuple at exactly the positive
  target coordinates. Its native relation is NEGATIVE but
  target relation POSITIVE. Full irreducible test coverage would
  reflect the relation, so the tuple is uncovered. Its
  function-closed source-generated hull admits the same genuine
  crossing FULL free decomposition.
- The crossing is stronger than graph disconnection: neither
  side contains all the generated input vertices, and all
  closure and function incidences are original native ones.

Both are genuine necessary obstructions, NOT an elimination of
those obstructions from connectedness, regularity or matching
original maximal canonical lifts. The upcoming substantive
geometric problem is to relate these crossed generated hulls
to the source minimal-separator/free-amalgam flip and prove
that either an earlier source minimum is violated or a
smaller positive-width separator must occur.

Four named standard-axiom checks and an active proof root
are registered. DRAFT until full exact-head Lean / integrity /
no-admission / proof-root inventory all pass.

## Exhaustive case split (added)

`ehn_nativeInputCoverage_or_functionCrossing_or_relationCrossing`
is now an actual native EHN trichotomy for EVERY source map,
with no assumptions about the forbidden family:

1. both function input-test coverage and positive target relation
   tuple preimage coverage hold and may feed the selected
   printed-tuple lex initialization;
2. an actual function-input-generated closed hull crosses a
   proper full free source decomposition; or
3. a relation input with target positive/source negative relation
   crosses such a native full free source decomposition.

These cases need not be disjoint. The trichotomy is not itself
the geometric contradiction: it isolates exactly which
crossed input-generated source hull must be analyzed by the
future true Claim 2 boundary/proper-subpiece argument. Five
named axiom checks now cover all proof endpoints.

## Corrected-image global lex-minimum dichotomy (further endpoint)

`Claim2StrongImageLexOrInputCrossing.lean` combines merged #1259
with the native function crossing certificate.

Under the stronger, EXPLICIT actual vertex-surjective EHN-image
closure, F-connectedness, F-free sides and genuine common maximal
canonical lift, begin with any nonempty forbidden weak EHN map.
Select an original GLOBAL (A-exclusive SOURCE,B-exclusive SOURCE)
lex minimum. Without assuming its function input-test cover:

* either its native function inputs are protected, in which case
  source-range closedness is *proved* and the validated same-target
  actual B-down/A-up forbidden-source flip follows; or
* an actual uncovered primitive function input of THAT SAME
  original lex-minimal forbidden witness has a crossed proper
  native free decomposition of its full function-closed hull.

This does NOT assert printed image closure suffices for the
positive branch; that requires the separate tuple-surjective
source/target relation control of PR #1268. It does NOT
claim the crossing alternative is impossible or that the
new source inherits original A-minimality.

One additional named axiom check and protected Lean root
are registered. Hold DRAFT until exact-head CI passes.
