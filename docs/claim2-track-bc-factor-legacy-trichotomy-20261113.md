# Track B/C: factor legacy positive-rank three-way proof through boundary-local theorem

**13 November 2026 — refactoring proposal.** Numbered 2019 `ramsey.tex`
is frozen; no collaborator-removed TODO notes are restored.

## Why this matters

The previously verified legacy theorem
`claim2_positiveRank_actualSuccessorWithExterior_or_smallerRoot_or_seamCollision`
still had a long independent repeat of the geometric partner-versus-smaller-root
proof. It used full common-seam injectivity `Set.InjOn f S` **only** for the
selected complete B-component generated boundary `T`.

The now merged theorem
`claim2_positiveRank_actualSuccessor_or_smallerRoot_of_activeBoundaryInjective`
proves the strictly stronger two-way conclusion from precisely the
boundary-local injectivity assumption, with the same genuine selected-Q
flip, original full global symbol, all exterior SOURCE count invariants,
and additionally a surviving A-exclusive source anchor.

This refactoring makes the older three-way theorem a short corollary:
* If `Set.InjOn f S`, then each B-active generated boundary lies in S
  because the seam preimage S is closed and
  `functionalClosure_neighborhood_subset_cut` applies. Derive the
  boundary-injectivity input of the two-way theorem.
* Project its successful actual flip (discarding only the *additional*
  anchor witness) or its precise smaller-root alternative.
* If full seam injection fails, return the legacy third obstruction.

The public old theorem statement remains **literally unchanged**.
No new axiom or source target-map injectivity is assumed; the older
global injectivity split is kept in the legacy theorem for compatibility.

## Substantive remaining gaps

This does not prove initial active boundary injectivity for arbitrary
forbidden EHN witnesses, does not show the mixed smaller-root alternative
can be repaired or ranked numerically, and does not derive terminal
outer-root target injection from source-symbol equality. The latter
must be provided at the start and preserved by exact target root
coordinates. The generic conditional finite descent from merged
Track B is unchanged.

## Exact-head validation

Require complete Lean library build, the existing protected theorem
`#print axioms`, full Section 3 source-contract scan and no-admission
audit. An independent non-appendix reference check should ensure the
legacy theorem name and statement are byte-for-byte preserved.
