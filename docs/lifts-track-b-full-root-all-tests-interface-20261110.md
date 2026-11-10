# Track B: export the actual full-root/all-test congruence (10 November 2026)

## Purpose

The Lean proof of `geometricFlip_preserves_globalPieceSymbol_of_newGeometricContext`
already contained a **stronger internal subproof**: after substituting an inner
piece in an actual FULL functional source amalgam, if the transported context
is literally the carrier of a genuine new outer geometric piece with the
prescribed ordered source root, then

1. the OLD and NEW `Fin n` full root structures are equal (including every
   primitive relation and entire partial/set-valued function fibre); and
2. the original and new genuinely geometric rooted pieces have exactly the
   same forbidden FULL-diagram tests for **every** rooted test, after the
   explicit dependent transport across that root-structure equality.

The prior module used these facts internally only to establish equality of
the globally indexed 2019 canonical piece symbols. This extraction exports
them as

`geometricFlip_preserves_fullRoot_allTests_of_newGeometricContext`

and makes the original global-symbol theorem a direct application of the
exported bridge plus the existing verified fixed-root-to-global quotient
conversion. The old global-symbol theorem's signature is unchanged. No
duplicate 70-line congruence proof remains.

## Exact hypotheses versus what is derived

Inputs: old and new native `Structure`s, actual old and new geometric
pieces, the original selected inner cut, the unchanged full complement,
one true replacement `Q`, its SAME full native diagram-profile equivalence,
and the literal full source amalgam `New = Q +_U E`. In addition the
**actual** new outer piece must have (i) precisely the transported original
ordered root and (ii) exactly the transported context as its WHOLE carrier.

Conclusions: full-root-structure equality and fixed-root all-test
congruence, both for these actual old/new geometrically selected pieces.

* The new theorem does **not** assume finite carriers, `F Old`,
  `F New`, positive width, target-level root injectivity, isomorphism closure
  of `F`, or any target homomorphism.
* It **does not construct** the new geometric outer piece, infer the
  exact carrier equation from closure, or derive a suitable positive-rank
  inner flip. Those are separate actual-geometry and Track C gates.
* No unrestricted Claim 2, global strong amalgamation, or shadow avoidance
  is asserted. The 2019 manuscript remains frozen.

The extraction reuses existing code for source-root identification and
transported native profiles; no new proof axiom, opacity assumption,
admission or classical nonconstructive witness is introduced.

## Validation gate

This is a **draft** until the exact-head full Lean build and
`CheckAxiomsLiftGeometricFlipGlobalSymbolCongruence.lean` (both
the new lemma and unchanged symbol theorem) succeed, along with
permitted-axioms inventory, no-admissions and active-proof-root audits.
No source proof should be marked newly validated merely from the
preexisting theorem's successful historical CI.

Next integration: use the exported all-test statement to instantiate
the `ProfileFixed` invariant in the concrete Claim 2 successor-state
interface. **Keep same-Q selection**, exact original full roots, actual
geometric status, and exterior source counts together; do not assume
the existence of a successor at every positive rank.

## Concrete selected-source corollary (same actual Q)

`nestedGeometric_selectedFlip_preserves_outerFullRoot_allTests`, in
`NestedSelectedGlobalOuterPieceSymbol.lean`, combines the merged actual
source-geometry theorem with the new generic export. For ONE genuine
selected replacement `Q`, ONE new forbidden source `New`, and ONE
source-side geometric nesting certificate, it **constructs** the new
geometric outer piece together with original ordered root coordinates,
complete native root-structure equality and all-test profile congruence.
No new geometric hypothesis is assumed in this selected-source corollary.
The old global symbol and exact context carrier are provided by the
same checked construction; its previously public API remains intact.

This is the precise `ProfileFixed` component needed for the Claim 2
state-transition invariant. It does *not* supply the eligibility of an
inner flip whenever B-rank is positive, the no-escape/anchor persistence
at arbitrary boundary widths, nor the terminal A-minimality exit.
Its added `#print axioms` is in
`CheckAxiomsNestedSelectedGlobalOuterPieceSymbol.lean`.

## 10 November evening: same-source complete step interface (second PR)

The new optional theorem
`nestedGeometric_selectedFlip_fullSourceStepInvariants_withAllTests`
strengthens the prior `nestedGeometric_selectedFlip_fullSourceStepInvariants`
without changing its public signature or copying its source counting proof.
It retains literally the SAME `Q`, `New`, `iQ`, `iE`, target maps
`f`/`flip`, and the SAME resulting `newOuter` geometric witness.

The theorem returns all of the prior source-step invariants:
ordered old outer root coordinates, actual global symbol, exact
outer-context carrier, unchanged target root tuple, strict decrease
of the B-exclusive SOURCE vertex count inside the piece, and
preservation of *all* exterior SOURCE counts indexed by any
`TargetSet`. On this **same newOuter** it adds the complete
old/new native root-structure equality and the fixed-root ALL-test
forbidden diagram profile. The new proof factors through the
already merged Track B export, using the existing exact carrier
and ordered root coordinate equations.

This is a one-step **conditional** invariant package. It does not
construct a positive-rank B-only inner piece at every state, make the
weak target root tuple injective, or supply the terminal A-only
support contradiction. It also must not be read as an unrestricted
proof of the original Section 3 strong amalgamation theorem.

Exact-head Lean build, named axiom check, permitted-axiom inventory,
source-contract and no-admissions scans are required before promotion.
The numbered TeX manuscript and existing author-removed TODOs are untouched.
