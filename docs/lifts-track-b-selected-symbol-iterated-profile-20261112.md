# Track B: carry the original selected global symbol through finite descent

**12 November 2026. Stacked on PR #1014.**

The original Section 3 Claim 2 descent has an existing generic
strictly decreasing B-exclusive SOURCE-rank iteration theorem. The old
four-predicate wrapper separately retained geometry, root coordinates,
the entire forbidden-rooted test profile, and exterior counts. For an
ACTUAL selected forbidden piece, the complete native SOURCE profile
follows from the original globally indexed selected symbol.

`claim2_selectedSymbol_terminal_preserves_width_root_allTests`
makes this precise for an abstract state space whose states may have
DIFFERENT positive root widths and genuinely selected source charts.
It assumes only:
* `Valid` at the initial state;
* any valid `Step` preserves validity, strictly drops the finite
  B-SOURCE rank and preserves the original selected GLOBAL symbol.

It produces an actual reachable terminal state with no `Step`
successor; its full original-source root width and complete rooted
native functional forbidden tests are identified with those of the
initial selected chart after the exact forced width transport.

This theorem does NOT claim that rank at an arbitrary terminal is zero,
because not every positive-rank state is known to admit a genuine
eligible inner flip. Its `Valid` predicate MUST still supply actual
geometric pieces, original ordered TARGET root coordinates, and
exterior SOURCE support invariants; none of those follows from
source-side symbol equality. Track C positive successor and Track D
weak target collisions remain independent.

The new proof factors through the existing verified natural-number
well-founded descent and the Track B cross-width dependent-symbol iff.
It adds no Lean axioms or admissions, introduces no new forbidden
family assumptions, changes no 2019 TeX, and does not restore author-
removed TODO notes.

**Validation:** draft until exact-head full Lean build, named permitted
axiom inventory, source integrity, active-root and no-admissions checks.
