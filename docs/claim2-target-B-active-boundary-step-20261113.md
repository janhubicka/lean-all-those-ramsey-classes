# Track C: actual B-to-A source flip transports all active B-boundary injections

**13 November 2026. Conditional Lean result in a draft stacked on #1101.**
The numbered original 2019 manuscript remains frozen.

The parent #1101 develops three source-only theorems:
- exact paired native function-generated boundaries under old/new
  root-containing cuts that agree on the complete retained E;
- local source-map injection transfer on those old/new boundaries;
- universal transfer for ALL target-active source vertices if the
  NEW inserted Q side contributes NO vertex of the target Active region.

The new wrapper
`fullNativeRightToLeftFlip_allBActiveBoundaries_injection_transfer`
derives the last 'no new active Q vertex' premise for the
specific RIGHT-to-LEFT direction in the 2019 proof. The selected
Q piece maps to the LEFT target witness, and an actual full
target free amalgam has no left points in the RIGHT-exclusive
target region. This is obtained from the verified
`fullFunctionalFreeAmalgam_swap` and
`freeRight_avoids_fullLeftExclusiveTarget`.

The only old injection requirement is **injection on the
complete generated seam boundary of every old B-active
retained E component**. After a genuine full-native source
flip whose full E target coordinates agree exactly and whose
complete glued root maps into the target common seam, the
NEW map is injective on the corresponding generated seam
boundary of EVERY new B-exclusive SOURCE vertex.

The theorem does NOT require the new map to be injective on
the entire new seam preimage. Fresh Q-nonroot collisions
mapping to the target common root are explicitly tolerated.
All cardinalities, when used in the surrounding descent,
are counts of SOURCE vertices, not target-image classes.

## Remaining concrete induction obligations

1. Show an initial forbidden-source witness with the exact
   active-boundary injection property, or obtain it from a
   justified initial normalization (the printed image-closure
   and irreducible-test cover hypotheses must be tracked).
2. Show that the SAME selected-Q new source carrying the
   geometry, exterior SOURCE-count conservation, A-anchor and
   local active-boundary injection is available in the
   matched-partner branch. This depends on precise same-witness
   gluing, not separately chosen existential flips.
3. Deal with strictly smaller positive roots that swallow
   common-seam vertices and may produce MIXED components.
4. Prove the original-A-minimizer terminal A-clearing exit.

No unrestricted Claim 2 or strong amalgamation is claimed.
The named axiom certificate and protected active-root inventory
must pass exact-head full Lean CI before merging this draft.


## 13 November CI repair

The first exact-head CI attempt compiled the parent #1101 module,
but the B-specific wrapper failed to infer the carrier universe of
`fullFreeRightExclusiveTarget`. The source statement has been
adjusted to the existing `Type`-level target-exclusive region API;
no mathematical premise or conclusion was changed.

The repaired full Lean build and its theorem-axiom checks have not
yet completed. Retain draft status. In particular, do not treat
this as a verified iterated-state theorem until the exact-head
CI gate passes and the same-Q source package is connected.
