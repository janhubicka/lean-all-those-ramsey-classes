# Track B: full source profile of any finitely reachable selected state

**12 November 2026.** The original 2019 manuscript remains frozen.
Do not restore collaborator-removed TODO comments.

## Interface strengthening

The already exact-head validated and merged Track B theorem
`selectedFunctionalChart_globalSymbol_eq_iff_width_root_allTests`
shows that one original global selected symbol determines the
entire native functional root width, exact ordered full root
structure, and equivalence with EVERY forbidden full rooted
diagram test.

The original conditional terminal theorem
`claim2_selectedSymbol_terminal_preserves_width_root_allTests`
proved finite path symbol conservation internally, only to use
it for a terminal state. This patch extracts two reusable
theorems for ARBITRARY reachable endpoints:

* `selectedSymbol_reachable_preserves_width_root_allTests`
  assumes a full source-selected chart in every state and
  literal original global symbol equality along every Step;
  no rank, validity or terminal assumption.
* `selectedSymbol_valid_reachable_preserves_width_root_allTests`
  assumes Valid at the initial state and that each valid
  step preserves validity and the original selected symbol.
  It derives validity of the endpoint and the same full
  source-root/test correspondence. No global symbol assumption
  is imposed on steps from invalid states.

Both proofs use ACTUAL finite `Relation.ReflTransGen`
reachability, including the empty path. There is no
arbitrary weak-image quotient and no requirement that
different state carriers have a common vertex universe.

The existing terminal theorem is refactored to use the
valid-path interface and has **exactly the same signature
and conclusion**. The general finite natural rank descent
remains separate and unchanged. The conditional zero-rank
terminal theorem still consumes the historical API.

## Adversarial scope audit

This source-side preservation does NOT force injectivity
of root images under a weak TARGET map, preserve exterior
A-exclusive SOURCE vertex counts, provide an admissible
B-source step at positive rank, make a smaller-root
obstruction inherit the old global symbol, or prove
the original A-minimizer contradiction. In any concrete
Claim 2 application, Valid must still encode genuine
geometric status and target/source accounting.

The relevant Track C trichotomy has disjoint alternative
branches: a strictly descending same-symbol flip, a
potentially different smaller-root piece, or a seam
collision. The new lemma applies to the flip branch
only, not to the other alternatives without new proofs.

## Verification

Require exact-head full Lean build, three named
`#print axioms`, permitted-axiom inventory, source
integrity, active-root checks, Section 3 contract audit,
and no-admissions scan before merge. The 2019 TeX and
external dependency pins remain untouched.
