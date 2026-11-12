# Track C — one actual matched-partner flip with exterior and A-only anchor

**12 November 2026. Draft Lean refactor pending exact-head CI; numbered paper frozen.**

Previously the verified matched-partner successor exported strict B-exclusive SOURCE support
decrease, original global outer symbol/ordered target-root coordinates, and conserved exterior
SOURCE counts. Separately, the verified same-Q inner source flip exported actual A-exclusive
anchor persistence. Their **independent existential witnesses cannot simply be combined**.

This PR refactors the existing `Claim2PartnerActualGeometricOuterStepExterior` module.
The new strongest theorem
`claim2_actualGeometricRightFlip_of_boundaryPartner_withExteriorAndAnchor` performs
the partner-boundary geometry exactly once and invokes the previously **verified**
`geometricGlobalRightFlip_actualOuterPiece_withExteriorAndAnchor` on that same
eligible geometric B-only inner piece. In one and the same genuine forbidden native source,
the resulting outer minimal-closed-separator geometric piece now has:

- the original ordered outer target-root coordinates and identical global piece symbol;
- strictly lower B-exclusive SOURCE count **inside the entire new outer piece**;
- for **every** target subset, exactly conserved SOURCE counts **outside** the entire piece;
- an actual A-exclusive SOURCE vertex inside the new outer piece, with the **same target
  coordinate** as the original anchor.

All of these conclusions refer to one selected Q/new source/new outer piece. No
intermediate global A-support minimality or smallest mixed piece is used.

The previous theorem `claim2_actualGeometricRightFlip_of_boundaryPartner_withExterior`
now becomes a direct **backwards-compatible projection** from the stronger theorem:
there is no second duplicative source flip proof. Both theorem names have named
`#print axioms` certificates; the existing active root remains protected.

**Still open:** constructing a suitable complete matched partner at every positive-rank
geometric state (smaller-root seam incursion is real); maintaining full-seam injectivity
when Q-nonroot vertices may map into the target root; and obtaining a general
zero-B-rank exit. Do not infer the conjunction of this theorem and independently
chosen #1020 trichotomy witnesses without recomposing the trichotomy with this
strongest wrapper.

No newly assumed target-image injection and no counting distinct weak target images.
The numbered manuscript is unchanged; previously removed collaborator TODOs are not readded.
