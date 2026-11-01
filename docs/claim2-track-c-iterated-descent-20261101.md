# Lift Section / Track C — Iterated Claim 2 (1 November 2026)

**Status: abstract finite iteration and a same-witness actual forbidden-source one-step contextual flip added in Lean; post-flip geometric/profile preservation and terminal exit remain OPEN.** Do not treat the section's strong-amalgamation/Ramsey theorem as validated.

Track A, at integration base `380804cceffe82e43023c0a3afe3c4e3946b3eec`, has supplied the genuine source geometry. PRs #737 and #738 are already on `main`. This track is separate from (A) construction of outer geometry, (B) all-test profile transport, and (D) noninjective root images.

## What is now proved

`Lifts/Claim2IteratedContextualDescent.lean` exports three Lean theorems:

1. `claim2_exists_terminal_of_strict_localB_descent`: a relation on possibly different forbidden-source carriers with a strictly decreasing natural-number rank reaches a terminal context by a **finite** sequence, provided every admissible step remains admissible. The proof does **not** assume another next flip.
2. `claim2_exists_terminal_preserving_outer_invariants`: the preceding theorem with **four separately named** obligations: genuine geometric piece, fixed original ordered root coordinates, fixed complete all-test rooted incompatibility profile, and unchanged native exterior.
3. `claim2_no_valid_initial_of_terminal_exit`: an explicitly **conditional** contradiction principle requiring the terminal-step exit argument.

These are genuine Lean theorems about arbitrary states and finite support descent, **not yet instantiated** for the actual geometric flip relation. Their kernel/axiom status must be confirmed by exact-head CI.

**Concrete package:** `Lifts/Claim2ContextualFlipPackage.lean` combines, for ONE specified new full native functional source and ONE pair of old/new target maps, function-closedness of the transported outer context, injective transport of the original ordered root, exact equality of its target coordinates, and strict local B-source-count decrease. It deliberately assumes the genuine inner piece is contained in the old outer piece and that the SAME replacement has the certified global B-count drop. This does not yet prove that the transported context is itself a geometric minimal-separator piece or preserves all rooted tests.

**Actual flip instantiation:** `Lifts/Claim2ActualOneStepContextualFlip.lean` invokes the original native right-to-left global lift flip ONCE and proves that its actual forbidden source/New EHN map simultaneously satisfies the package's conclusions. In this derived theorem the strict global support drop is **proved** from the same flip, rather than being an additional external assumption. It assumes inner-piece target-root injectivity, genuine inner containment, outer-root disjointness from the removed component and the already available common full canonical lift. It does not solve the new outer geometric piece or all-test profile problems.

## Existing concrete one-step input

- `GlobalFlipOuterRootStrictSupport.lean`: one *actual* new forbidden source and map have a strict global B-source drop and unchanged exterior/root target coordinates.
- `GlobalFlipClosedOuterContext.lean`: the transported outer context is function-closed, contains the outer root.
- `GlobalFlipContextInducedFreeDiagram.lean`: the closed context inherits an actual full native functional diagram under its explicit hypotheses.
- `GlobalFlipContextOutsideSupport.lean`: outside-context source counts agree.
- `GlobalFlipLocalRightSupport.lean`: under a genuine **inner subpiece**, the same map has a **strict local** B-only SOURCE count drop.
- `ActualNestedFunctionalProfileCongruence.lean`: forbidden-family membership transfers in specified nested full diagrams; this does not by itself give equality of **all rooted outer incompatibility tests**.

## Remaining proof obligations for Track C

**C1: actual successor API (partially implemented).** The package `geometricInnerSubpiece_closed_fixedRoot_strictLocalRightSupport` combines four certificates for one specified replacement. The new `geometricGlobalRightFlip_outerContextClosed_strictLocalRightSupport` applies it to ONE actual full-lift B-to-A forbidden-source replacement, with strict local B-only source decrease and original-root transport for that SAME witness. Still required: identify this transported context as a genuine minimal-separator geometric outer piece, prove appropriate nested diagrams for arbitrary attached tests, and construct a *reusable* successor valid at every iteration. The two strict-count lemmas must never be applied to different existential replacements.

**C2: genuine outer piece after one step (open; dependent on Track A).** Prove the transported context has the required selected connected component and **inclusion-minimal function-closed separating root**, not just closedness or equality of a selected set. Carry the *original* root and full native incidences. The replacement must still supply a geometric piece inside the forbidden source rather than an artificial weak-image quotient.

**C3: full all-test profile (open; dependent on Track B).** Prove preservation of the **entire** rooted incompatibility profile under each concrete replacement, by nested source-diagram reassociation and inverse reassociation for arbitrary attached root tests. A single use of `F New` or the trace of one test is insufficient.

**C4: descent and terminal exit (conditional theorem now in Lean; concrete instantiation open).** Define valid states with source, map, geometric piece, original root/profile/exterior invariants, and rank
`Nat.card {v : sourceCarrier // v ∈ outerPiece ∧ map v ∈ BExclusiveTarget}`.
Show every certified concrete successor is valid and decreases this *local* rank. Then instantiate the termination theorem. Finally supply a **new** terminal obstruction/last A-to-B flip contradicting the original LEFT-support-minimizing witness. Do not assume preservation of left minimality along B flips; prove whatever bound the final contradiction actually needs.

## Integrity checks

- Keep the frozen `ramsey.tex` mathematical prose unchanged; use nonprinting TODO/validation markers for unresolved assertions when integrating manuscript changes.
- `#print axioms` each new theorem and enforce the usual allowed axiom set.
- Confirm source imports, active-root inventory and exact-head CI before integration.
- Do not mark unrestricted Section 3, its printed Claim 2 or the strong-amalgamation/Ramsey endpoint green.
- Continue to track the independent noninjective-root and finite-family Ramsey dependencies (Tracks D/E/F).

### Audit warning

The rank is **inside the transported outer piece**, not the global B-source count and not the number of target images. The abstract finite-descent theorem guarantees termination from preservation and strict decrease; it does not prove that concrete successors preserve the required geometric/profile fields, nor does it manufacture the terminal A-to-B contradiction.
