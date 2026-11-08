# Track A/C — concrete selected-Q successor and remaining Claim 2 gates

> **Later 8 November status update:** PRs #925, #927, and #929 are
> now merged after successful exact-head Lean CI. Their draft labels
> below describe the earlier submission stage. The remaining
> positive-rank existence, iteration/terminal proof and weak-map root
> collision obligations remain open. See the
> [Track A closeout](lifts-track-a-closure-20261108.md).


**8 November 2026. Review-only validation ledger.** The numbered original
2019 manuscript remains frozen. New PRs are not declared verified until
exact-head compilation, active-root inventory, a permitted-axiom sweep,
and the named `#print axioms` checks succeed.

## Now kernel-verified and merged

- **#899** actual nested original functional forbidden source, SAME
  genuinely selected replacement Q, original ordered outer root and
  complete original globally indexed canonical outer piece-symbol
  preservation; all-test incompatibility under the full native function
  graph language (not weak target-map quotient).
- **#909** transfer of that exact old outer symbol's relation to the
  weak target **when the old outer root image is injective**.
- **#913** begin with the actual global canonical relation in a
  second witness, derive Q and a literal forbidden full source
  replacement and obtain that original outer target relation,
  again with the explicit old outer-root image injectivity premise.
- **#921** the actual common FULL global canonical flip now returns
  the genuine *geometrically selected* Q certificate. Its
  right-to-left version returns the SAME Q and whole complementary
  source-map agreement, rather than losing the selected witness.
- **#922** reuses exactly that selected source flip in the
  previously verified strict B-exclusive **SOURCE** count lemma on
  the transported closed context. The output retains the genuine
  Q certificate from the very SAME strict-rank witness.

## New proof submissions, CI NOT YET VALIDATED

- **#925**: local B-exclusive SOURCE count on the transported
  closed context becomes the count on the exact transported
  old root + ONE new connected outer-cut component.
  The original CI found the set rewrite oriented incorrectly:
  it was corrected by rewriting the GOAL from component back to
  context before applying the strict count theorem.
- **#927**: strengthen the already verified global-symbol theorem
  to return its internal **full geometric outer piece carrier**
  equality. Then a strict count on the SAME Q's context is a
  strict count on that same actual new geometric piece. This
  currently repeats the audited #899 proof to expose one
  additional conjunct; after a successful new CI, replace the
  old proof with a corollary of this stronger API so the library
  does not retain duplicated logic.
- **#929**: combine #922 with #927, yielding ONE actual selected
  right-to-left forbidden source flip, its weak map agreeing
  with the old map on the entire complement, the new genuine
  outer geometric minimal-closed-separator piece with the
  ORIGINAL ordered outer root and same GLOBAL canonical symbol,
  target root coordinates unchanged, and strict B-only SOURCE
  count decrease on its ENTIRE actual source piece.

## Adversarial proof obligations after the concrete step

1. **Flippability at every positive rank (Track C).** The
   concrete strict one-step theorem assumes a genuine selected
   B-only inner geometric piece with positive complete inner
   root, all its vertices inside the outer piece, and a
   B-exclusive witness; it does NOT construct one from
   `local B-rank > 0`. The partner/smaller-root dichotomy
   and singleton boundary arguments cover special cases but
   mixed multi-root cases still need a genuine source proof.
2. **Iteration state and exterior invariants (Track C).** Package
   every state as an actual finite forbidden source, weak map,
   genuine outer geometric piece, fixed target coordinates and
   original global piece class, unchanged relevant exterior, and
   rank counting **SOURCE** vertices in its full geometric carrier.
   The new #929 endpoint supplies the geometric, root, profile
   and local strict-rank portions for one actual selected flip.
   The preserved exterior and applicability of the *next* step
   must be established in the concrete Step predicate. Do NOT
   count target images or compare separately chosen existential Qs.
3. **Terminal exit (Track C).** The abstract well-founded
   natural-number descent theorem already reaches a terminal
   state when every valid step decreases rank. It does NOT
   contradict the *original A-exclusive support minimizer*.
   The final A→B one-sided flip and the actual A-rank accounting
   are a separate necessary proof.
4. **Weak target root collisions (Track D).** The selected
   original global lift relations require DISTINCT root images.
   Neither source geometric root injectivity nor a generic
   EHN weak source map implies target root injectivity. The
   hypothesis in #909/#913 must not be dropped until the
   common-lift/forbidden-image argument proves it.
5. **Source language fidelity.** All cuts, components and
   amalgams are in the native complete set-valued functional
   graph language, including nullaries and arbitrary arities;
   no homomorphism-embedding is silently promoted to a FULL
   source embedding or weak target-image quotient.

**Status marker:** Track A source geometry and globally indexed
old symbol transfer are merged and verified, with the explicit
root-injectivity assumptions. Concrete Track C successor with
rank is in draft PR #929. The unrestricted printed Claim 2
and strong-amalgamation endpoint are NOT yet validated. Do not
re-add manuscript TODOs removed or commented out by collaborators.


## 8 November continuation: new exterior-A support integration

The first direct concrete geometric one-step statement (#929)
has now been fully Lean-CI verified and merged, together with its
support carrier preparation (#925) and same-Q global-symbol/carrier
construction (#927). The new work below is **draft only**:

- [#942](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/942)
  specializes the already verified
  \`geometricInnerSubpiece_outsideSupport_card_eq\` to the exact
  **new geometric outer-piece** carrier. Thus for EVERY target
  subset S, source support OUTSIDE the whole old and new pieces
  has equal finite cardinality. An initial duplicated bijection
  proof was removed in favor of the existing verified theorem;
  the only new work is the exact geometric carrier rewrite.
- [#945](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/945)
  packages the source geometric piece, literal old ordered root,
  unchanged weak-target root coordinates, original global
  canonical symbol, STRICT local inside B-only SOURCE count
  decrease, and exact unchanged exterior source counts for ALL
  target subsets. This package takes ONE selected Q/new source
  as input, so it cannot silently switch existential witnesses.
- [#948](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/948)
  applies this package to the already verified real same-Q
  right-to-left common-full-lift source replacement (#922/#929).
  It remains *conditional on a suitable inner flip*; no general
  existence or final contradiction has been added.

### Important terminal accounting — previously verified

The existing \`Claim2TerminalLeftSupportAccounting.lean\` proves:
- \`claim2_exists_terminal_with_constant_outsideLeft\`: a
  strict local B-source count descent preserving outside A-count
  reaches a terminal state whose outside A-count equals the
  **original** outside A-count;
- \`finiteSourceSupport_terminalLeftDrop_of_outsideEq\`: if the
  initial outer piece contained an A-only SOURCE vertex and a
  final replacement has **no** A-only source vertex in the
  final context, while the exterior A-count is unchanged,
  the TOTAL final A-only SOURCE support is strictly smaller
  than the original;
- \`minimalForbiddenEHNWitness_no_terminalLeftClearingFlip\`:
  this strict total A-count drop directly contradicts the
  genuine original A-support-minimizing forbidden witness.

Consequently **no intermediate A-minimality is required**, even
though intermediate B-to-A flips may increase A-only source
support inside the current outer context. The essential
still-unproved terminal hypothesis is the EXISTENCE OF A
FINAL A-CLEARING FORBIDDEN SOURCE FLIP with unchanged exterior,
not intermediate A-minimality or a trivial restatement of
decreasing B-rank.

### Precise remaining construction gates

1. **State-wide positive B-rank successor:** #929 and draft #948
   require a *specified genuine flippable inner geometric piece*
   with positive inner root width, the correct one-sided source
   component, root image injectivity, and full common lifted
   witness. They do NOT derive such a piece merely from
   \`localBCount > 0\`. The verified
   \`positiveRank_noEscape_singletonBoundary_hasProperFlippablePiece\`
   handles special singleton-boundary/no-escape states; the
   arbitrary mixed higher-width root case remains.
2. **Repeated applicability/no-escape:** a single source flip
   with a valid new outer geometric piece and exact original
   canonical symbol does not automatically preserve all
   auxiliary no-escape conditions that select the next inner
   piece. These must be included explicitly in the concrete
   Step relation and proved after each replacement.
3. **Final A-clearing terminal exit:** establish the existence
   of a real final forbidden source map with zero A-only
   source vertices INSIDE the terminal context. The verified
   support-counting contradiction can then be applied, thanks
   to exact preservation of exterior A-count. No final-exit
   construction is currently implied by natural-number
   termination alone.
4. **Weak target root collisions:** global canonical piece
   relations require distinct coordinates. The SOURCE root
   tuple is injective, but its weak-target image may not be;
   #909/#913 remain explicit about this. Track D must resolve
   it from the real maximal common-lift/image hypothesis.

**Validation rule:** Do not promote #942/#945/#948, the
positive-rank step-existence claim, the terminal exit, or the
unrestricted printed Claim 2 until exact-head kernel CI and
statement-by-statement correspondence pass. Retain all prior
collaborator-removed manuscript TODOs as removed. The numbered
2019 manuscript remains untouched.
