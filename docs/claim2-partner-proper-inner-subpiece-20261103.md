# Track C: partner-rooted proper B-only subpiece without intermediate A-minimality

Stacked on the full native boundary localization of #824.

For an actual outer geometric piece P=R∪C, any full shared-root-preimage S containing R and any S-component B⊆C:

- the exact function-generated boundary T=Cl(N(B)) lies in S∩P;
- if the explicit opposite boundary-partner criterion holds for T, an actual finite minimal-closed-separator geometric piece d has FULL root T and EXACT selected component B;
- if P also contains an A-exclusive vertex a outside S, then d omits a, hence its FULL vertex set is a PROPER subset of P;
- if f is injective only ON T, the ordered TARGET root images of d are injective.

The result does **not** need left-support minimality of the **current** forbidden source, nor mixed-piece cardinality minimality; it treats the original source map f as potentially noninjective away from S. AOnly is an explicit source vertex set; B being one-sided is an explicit easy condition established independently by the full free-amalgam monochromatic component theorem when f is the real weak EHN map.

**Mathematical status:** the root's partner existence and InjOn(T) are genuine extra hypotheses. Neither follows merely from positive B-source support, closedness of S or regularity. Thus this is a nontrivial conditional proper-B-subpiece construction, not the positive-rank successor theorem.

Lean: `geometricPiece_properInnerOneSided_of_boundaryPartner`, named axioms, retained root. Exact-head CI pending. No changes to frozen manuscript.

## Same-witness contextual canonical flip

The new `Claim2PartnerActualContextualFlip.lean` composes this actual genuine proper subpiece with the **already merged** `geometricGlobalRightFlip_outerContextProfile_strictLocalRightSupport` (PR #777). For one real weak EHN forbidden witness, the result constructs a proper inner B-only geometric source piece and ONE native canonical B→A forbidden-source replacement which:

- strictly decreases local B-exclusive SOURCE support inside the transported outer context;
- preserves the complete outer all-test rooted incompatibility profile;
- preserves the original ordered root target coordinates on the retained FULL complement;
- does not require intermediate left-support minimality or a supposed globally injective weak quotient.

The theorem still requires the actual opposite-boundary partner for the B component, plus InjOn on the **selected** generated boundary T. It does not derive pairwise image separation on each NEW selected T after earlier flips, nor recognition of the newly transported context as a genuine geometric piece. These are the exact remaining successor obligations; no unrestricted Claim 2 proof is claimed.

## Verified-base singleton-boundary specialization (new Lean attempt)

`Claim2SingletonBoundaryContextualFlip.lean` eliminates BOTH additional partner and selected-root InjOn hypotheses whenever the current right-exclusive S-component has a **nonempty singleton generated boundary** T and its right source vertex is connected to a left-exclusive vertex inside the same current outer geometric piece.

The existing native `weakRightComponent_singletonBoundary_hasPartner` constructs a genuine opposite component with complete matching generated boundary, without any A-minimality. The singleton property itself makes `f|T` injective, irrespective of global weak-map collisions. Therefore the partner-based theorem supplies a real proper B-only inner piece and a same-witness contextual canonical B→A flip: complete outer all-test profile, ordered outer root coordinates and strict inside B-source support decrease.

This is a meaningful positive-B-rank **one-step** result in the singleton-boundary case. The replacement's transported outer context is still only closed; Track A must recognize it as a genuine minimal-separator geometric piece before iterative application. The hypothesis that positive B-source support always admits a singleton boundary is NOT asserted. Exact-head CI for this new specialization is pending.
