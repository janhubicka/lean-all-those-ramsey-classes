# Track C: a reachable obstruction rather than a hidden positive-step premise

**12 November 2026. Independent proposed Lean theorem; exact-head CI pending.**

## Mathematical reduction

The already-checked finite natural-rank descent (Claim 2) needs
that all actual steps preserve state validity, strictly reduce local
B-only SOURCE rank, and conserve A-only SOURCE support outside the
entire geometric context. Previous #958 obtains a reachable rank-zero
terminal state assuming EVERY positive-rank state has a valid step.
Our proposed positive-rank geometric trichotomy #1015/#1020 instead
says the step exists OR a real geometric smaller-root/collision
obstruction is present.

The new abstract
`claim2_exists_reachable_obstruction_of_stepOrObstruction_and_zeroExit`
turns this into a precise finite obstruction dichotomy.
Assume a true source-specific state model, valid strict steps and
exterior support conservation, an `Obstruction s ∨ ∃ t, Step s t`
alternative for EVERY valid positive-rank state, and a verified
ORIGINAL-minimizer zero-rank exit at the conserved original
exterior A-count. Then **from every valid initial state one can
reach a valid state exhibiting Obstruction** in finitely many actual
steps. In particular, the bad branch cannot be swept away by
abstract well-foundedness.

Proof: restrict Step to states with `¬ Obstruction`. Apply verified
`claim2_exists_terminal_with_constant_outsideLeft`. A zero-rank
terminal state violates the explicit zero-exit. A positive-rank
terminal state with no obstruction has a restricted next step by
the local alternative, also impossible. Finally the restricted
finite path maps to a genuine Step path.

This is independent of claims of source-map root-injectivity or
unrestricted strong amalgamation. A concrete full-functional
state structure and an actual source-specific zero-exit
instantiation are still needed for Claim 2. The numbered paper
is frozen; no removed TODO was reintroduced.
