# Track B: literal Q-provenance for every successful positive-B-rank step

15 November 2026. Additive main-based Track B branch. The numbered
2019 manuscript is frozen; no author-removed TODOs reinstated.

## Mathematical change

The previously merged heterogeneous state theorem guaranteed
that, at positive local B-exclusive SOURCE rank, either an actual
state step exists or a smaller separator causes old-root capture
or A-mixedness. But the step relation only retained invariants,
not the actual selected forbidden Q in its Q+E native source
free-amalgam. It would have been unsound to assume every abstract
step stored a selected-Q witness.

Two new modules close exactly this *proof-provenance interface* gap:

1. `Claim2PositiveRankEligibleInnerSelection.lean` proves that
   positive B-source rank yields an **actual eligible nested
   geometric source piece** (complete root in TARGET seam,
   ordered root target injection, A-free selected B-component,
   no capture of the old outer root, actual proper inner
   component containing a B-exclusive SOURCE vertex), OR one
   of TWO genuinely witnessed source-geometric obstructions:
   old-root capture or A-mixedness. It reconstructs the piece
   in the matched generated-boundary case using the existing
   source geometry BEFORE ANY Q selection, and handles the
   strictly smaller boundary using the checked escaping-source-
   component/old-root capture lemma. No weak target-image
   quotient or artificial source replacement.

2. `Claim2SelectedQPositiveRankObstructionDescent.lean`
   applies the verified single-source theorem
   `claim2Native_eligibleInner_hasSelectedQProvenanceStep`
   to that SAME eligible piece. Its positive-rank theorem
   now outputs an actual state step retaining the LITERAL
   forbidden selected Q, complete Q+old-complement free native
   diagram, target agreement on all retained E vertices,
   Q no-B images, exact new outer carrier, old global symbol,
   original ordered target root coordinates, every exterior
   SOURCE-cardinality profile, surviving original A anchor,
   and preserved root and local B-active boundary injections.
   On capture/A-mixed branches it reports the literal source
   witnesses instead of fabricating an eligible inner piece.

The finite source-rank descent now applies directly to the
STRONGER Q-provenance step relation, so a positive-rank chain
stores an actual selected-Q diagram at each edge and obeys
`chain length + terminal B-source rank ≤ initial B-source rank`.
The original zero-rank A→B flip/minimality contradiction removes
the zero-rank endpoint when the **initial** full geometric
state comes from an ORIGINAL globally A-SOURCE-minimal
forbidden EHN witness. It reaches capture or mixedness.

## Nonclaims / remaining mathematics

- Does NOT manufacture the original initial source state;
  local generated-boundary/root injection still require the
  previously formalized initial collision/coverage gates.
- Does NOT eliminate old-root capture or A-mixedness at an
  arbitrary intermediate state (those are now the only
  positive-rank exits). Track C has separate conditional
  all-width extremal source arguments which must not be
  silently applied after B→A changes original A-minimality.
- Does NOT prove all *contract-only* native state steps are Q
  replacements; it instead proves an actual Q-preserving
  successor exists whenever not obstructed, then iterates
  the stronger relation.
- No extra axiom, global seam injectivity, distinct-image
  counting, change of F or frozen 2019 TeX.

Keep DRAFT until exact-head full Lake/Lean, permitted-axiom
inventory, named #print axioms, active-root and no-admission
source-integrity checks pass.
