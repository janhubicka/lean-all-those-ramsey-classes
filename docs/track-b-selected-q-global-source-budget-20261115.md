# Track B: total B-exclusive source support decreases along selected-Q provenance chains

15 November 2026. Stacked on Track B original-minimizer same-Q
source-chain PR #1237, itself stacked on positive eligibility
PR #1231. Frozen numbered 2019 paper unchanged.

New module `Claim2SelectedQGlobalBSourceBudget.lean`:
- defines `claim2NativeTotalBSourceCount` by `Nat.card` of
  LITERAL SOURCE vertices mapping into the full right-exclusive
  target region, not by the number of distinct weak-map images.
- proves `claim2NativeSelectedQStep_strictGlobalBSourceCount`
  by direct specialization of already checked
  `finiteSource_strict_global_active_of_inside_and_exterior`.
  Every genuine selected-Q source replacement has strict local
  B-exclusive SOURCE-rank loss and exactly conserved exterior
  SOURCE-cardinality for all target regions (take right-only);
  therefore its TOTAL B-exclusive SOURCE support decreases.
  The same actual new native source/weak EHN map and Q+E
  free-amalgam certificate appear in the step predicate.
- proves `claim2NativeSelectedQChain_globalBSourceBudget`:
  for k actual selected-Q native free-amalgam transitions
  `k + totalB(terminal) ≤ totalB(initial)`. The stronger
  local rank budget remains independently available.

**Important caveat:** A B→A flip may INCREASE total A-only
SOURCE support (an inserted Q may contain new A-only source
vertices). Strict B-decrease thus does NOT establish that
intermediate witnesses remain original globally A-minimal,
nor does it allow lexicographic (A,B) minimization without
an A-neutrality certificate. It does not exclude source
root/boundary test gaps or old-root capture/A-mixedness.
No weak source-image quotient or new forbidden family assumption.

Named #print axioms and protected root; exact-head Lake/Lean,
permitted-axiom, no-admission, import/source-contract and
inventory CI required before merging.
