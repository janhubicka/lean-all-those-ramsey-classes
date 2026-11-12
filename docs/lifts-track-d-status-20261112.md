# Track D — verified reductions and remaining Section 3 root-collision gate (12 November 2026)

This is the CURRENT checkpoint; the older
[`lifts-track-d-root-collision-20261101.md`](lifts-track-d-root-collision-20261101.md)
is preserved as a historical audit. All results below refer to the
actual native functional language and original 2019 `ramsey.tex` Section 3.
**The printed manuscript is frozen**; this note adds no validation marker
or collaborator TODO back to that document.

## The image-closure contract and the counterexample

The printed image closure applies to tuple-surjective
original-partial homomorphism-embeddings and concludes that the
target **contains** an induced forbidden member. It does NOT claim
that every vertex-surjective weak EHN image is itself a forbidden
member, that the full range reflects all relation tuples, or that
the weak quotient fully embeds into an arbitrary target.

The exact source-generated quotient is tuple-surjective, but its
inclusion in the target is only weak in general. This is not a technical
gap which can be solved by simply asserting full range closure.

**Verified on main:** `fiveCycleImageFamily_counterexample_to_blanketInjectivization`
in `Lifts/EHNFiveCycleNoInjectiveReplacement.lean`, with supporting
`EHNFiveCycleImageClosedFamily` and `EHNFiveCycleImageFamilyConnected`,
gives a finite connected family satisfying the *printed* image
closure and a noninjective forbidden EHN witness with NO injective
replacement in the same target. This refutes the unrestricted
injectivization shortcut, **not** strong AP for compatible canonical
maximal lifts.

## Current positive formalized reductions

* **Actual root/image geometry:** `minimalGlobalForbiddenWitness_collidingRoot_or_mixedPiece`
  yields a genuine positive-width geometric forbidden piece in the
  actual full free amalgam. Its collision alternative is not suppressed.
  `ehn_injOn_of_rootPairsCoveredByIrreducibleTests` conditionally
  rules out root collisions when full irreducible source tests cover
  each root pair; the cover itself is NOT automatic.
* **Actual quotient reflection defects:** merged PRs
  [#898](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/898),
  [#907](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/907),
  [#908](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/908),
  [#915](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/915)
  establish that a bad FULL irreducible weak-image test factoring into
  a genuine free-amalgam side exposes extra target relation/function
  incidence; the covered-function-input case eliminates the
  function surplus only under its EXPLICIT source test cover.
* **Local uncovered function inputs:** merged
  [#912](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/912)
  establishes that a side function surplus forces unprotected original
  source input tuples whose original function fibre is EMPTY. It
  also supplies genuinely native source hull decompositions, and
  a language-restricted injectivization theorem for nullary/unary
  functions without relations or total source functions without relations.
* **Actual crossing representatives:** merged
  [#989](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/989)
  exhibits actual source preimage representatives of relation/function
  surplus coordinates with a proper FULL free decomposition crossed
  by their input generators; a collision on any pair of distinct
  generators similarly forces a genuine crossing root-hull decomposition.
  This does NOT identify the decomposed hull with a genuinely
  selected forbidden geometric piece.
* **Exact conditional normalization-to-geometry handoff:** merged
  [#1004](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1004)
  produces a globally source-support-minimal **injective** EHN
  forbidden witness and its smallest genuine mixed geometric piece,
  assuming the *printed* image closure PLUS explicit full irreducible
  source-test coverage for EVERY native function and relation input.
  Those coverage assumptions are NOT consequences of forbidden-source
  connectedness/regularity.

Every item described as *merged* is backed by a successful exact-head
Lean build, named permitted-axiom checks, source-contract/integrity
audits and no-admissions scan. The results are conditional exactly
as stated; the module or PR must be consulted before using them.

## In-flight additions, not counted as verified on main

As of the 12 November checkpoint:

* [#1001](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1001)
  adds the **unary relation-input** analogue and injective
  support-minimizer corollaries for arity-at-most-one languages and
  total-on-forbidden-source functions with unary relations.
  It passed an earlier exact-head stacked CI but was rebased to
  main; merge requires a fresh successful exact-head gate.
* [#1017](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1017)
  proposes to replace the **actual separator-root collision** branch
  of the support-minimal 2019 free-amalgam dichotomy by an explicit
  proper native full free decomposition of the very same source
  root-generated hull, where neither side contains all root generators.
  This is a draft until its own exact-head checks pass.

* [#1028](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1028)
  weakens #1004 to **ONE already support-minimal forbidden witness**:
  its own full irreducible function-input test coverage and target
  relation-tuple surjectivity on its actual range are sufficient to
  construct an injective support-minimal replacement with a smallest
  genuine mixed piece. The two conditions are still explicit.
* [#1034](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1034)
  is stacked on #1028. It proposes a three-way minimal-witness
  obstruction under only the printed family hypotheses: an actual
  uncovered source function input with a reducible full generated
  hull, an actual target-only positive relation at source image
  coordinates with a reducible full generated hull, or an injective
  support-minimal witness and its smallest genuine mixed piece.
  This is an exhaustive **reduction**, not exclusion of either
  crossing-input alternative. Both #1028 and #1034 are drafts
  until exact-head Lean CI and axiom/source audits pass.

## Critical remaining proof obligation

An **unrestricted** proof of original regular-family strong AP
requires either:

1. a genuine maximal-common-lift argument excluding these
   reducible, uncovered separator-root / source-input configurations
   under the exact original 2019 hypotheses; OR
2. a collision-tolerant forbidden-source flip preserving the
   ACTUAL old-language finite source, the full canonical root
   profile, and strict decrease of the ORIGINAL source A-exclusive
   support count, without false target-root injectivity.

Crossing free decompositions of a *root-generated closed hull*
alone are **not** flippable geometric forbidden subpieces. The
literal root cut, selected private component, ordered symbols,
target-root map and source-side support accounting must all be
re-established before invoking any Track C descent.

Even a solved Track D collision case would leave Track C's
arbitrary-positive-rank genuine selected-Q successor and terminal
A-minimizer contradiction as independent obligations.

**No unrestricted Claim 1 / Claim 2 / Section 3 strong AP or Ramsey
statement is currently kernel-certified.**
