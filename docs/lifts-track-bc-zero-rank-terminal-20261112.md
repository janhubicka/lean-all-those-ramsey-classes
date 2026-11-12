# Track B/C: original selected symbol at a zero-B-rank terminal

**12 November 2026.** This independent additive source module is stacked
on the selected-width/profile theorem (#1014) and its iterated terminal
handoff (#1026). The numbered 2019 source remains frozen.

## Verified dependencies and precise new conditional statement

The old Track C theorem
`claim2_exists_zeroB_terminal_with_constant_outsideLeft` already
isolates strict finite B-SOURCE-rank descent, exterior A-SOURCE count
conservation, and an explicit positive-rank successor oracle. Track B
now proves that the ORIGINAL global selected symbol alone determines
the full source-root width and all full native forbidden diagram tests.

`claim2_selectedSymbol_exists_zeroB_terminal_with_exterior_and_allTests`
packages these without requiring separate width or profile invariants:
given valid initial state, strictly decreasing valid steps preserving
the original selected global symbol, equal exterior A-only SOURCE
count across every step, and an actual successor from every valid
positive-B-rank state, there exists a reachable terminal with:
* true B-exclusive SOURCE rank ZERO (not assumed);
* exactly the original exterior A-exclusive SOURCE count;
* exactly the initial full ordered native functional root, after
  transport across the equality of the initially arbitrary widths;
* agreement of the original and terminal selected pieces against
  EVERY full native forbidden-rooted source diagram test;
* no further admissible successor.

The proof reuses #1026's genuine terminal construction, derives zero
rank by contradiction with the explicit positive-rank successor
assumption, and transports exterior counts inductively along its
ACTUAL finite reachability chain.

## Critical nonclaims

This theorem does NOT prove that every positive B-rank state has a
successor, nor that the terminal outer-root image is injective in an
EHN weak target map. Actual geometric status, target coordinates
and the EHN witness live in `Valid` and must be discharged when the
conditional abstraction is instantiated. It does not prove final
original A-minimizer contradiction or unconditional Section 3 strong
amalgamation. It does not conflate source-vertex counts with target
image counts. No missing assumption is disguised by `ProfileFixed`.

## CI gate

Keep draft until exact-head full Lean library build, named permitted
axiom check, import/source integrity, source-contract, active-root
and no-admissions scans succeed. Parent PR #1026 must merge first.
