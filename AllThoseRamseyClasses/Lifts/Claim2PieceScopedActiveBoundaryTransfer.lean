import AllThoseRamseyClasses.Lifts.Claim2RetainedCutBoundaryPair

/-!
# Transfer B-active boundary injection only inside the chosen outer piece

The verified positive-rank source dichotomy needs injectivity on
generated boundaries of B-exclusive SOURCE vertices inside ONE
chosen genuine geometric outer piece P, not everywhere in the source.

The generic paired-boundary transfer theorem on #1101 is phrased
globally over ALL retained E vertices. Here we prove a piece-scoped
version using an explicit carrier inclusion matching the actual
selected-Q outer replacement:
  NewPart ⊆ image(NewQ) ∪ image(E vertices from OldPart).

When the inserted NewQ maps entirely outside the chosen active
target region, each B-active vertex of NewPart is in E over OldPart.
Thus the old local-in-OldPart boundary-injectivity assumption suffices
to propagate the exact new local-in-NewPart invariant.

This theorem does NOT establish the carrier inclusion for any
arbitrary replacement, nor provide positive-rank successor existence,
initial boundary injectivity, terminal root injectivity, or the
smaller-root mixed-piece repair. Full SOURCE vertex sets are used.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Scoped version of exact full-native generated-boundary
injectivity transfer. Crucially, the OLD hypothesis is only for
active vertices INSIDE OldPart. The new carrier relation and
opposite-side Q activity exclusion are explicit geometric inputs.

These two data are expected from SAME-selected-Q full native
outer-carrier reconstruction, not inferred from arbitrary weak
target-map agreement. -/
theorem fullNativeReplacement_pieceScoped_activeBoundaryInj_transfer
    {H E₁ E₂ F W₁ W₂ UT : Type v}
    {Root : Structure L H}
    {OldLeft : Structure L E₁}
    {NewLeft : Structure L E₂}
    {Right : Structure L F}
    {OldWhole : Structure L W₁}
    {NewWhole : Structure L W₂}
    {sOldL : Structure.Embedding Root OldLeft}
    {sNewL : Structure.Embedding Root NewLeft}
    {sR : Structure.Embedding Root Right}
    {iOldL : Structure.Embedding OldLeft OldWhole}
    {iOldR : Structure.Embedding Right OldWhole}
    {iNewL : Structure.Embedding NewLeft NewWhole}
    {iNewR : Structure.Embedding Right NewWhole}
    (hOld : Structure.IsFreeAmalgam sOldL sR iOldL iOldR)
    (hNew : Structure.IsFreeAmalgam sNewL sR iNewL iNewR)
    (f : W₁ → UT) (g : W₂ → UT)
    (Seam Active : Set UT)
    (OldPart : Set W₁) (NewPart : Set W₂)
    (hSameE : ∀ e : F, g (iNewR e) = f (iOldR e))
    (hOldRootSeam : ∀ r : H, f (iOldR (sR r)) ∈ Seam)
    (hNewCarrier :
      NewPart ⊆ Set.range iNewL ∪
        iNewR '' (iOldR ⁻¹' OldPart))
    (hNewQNoActive : ∀ q : E₂, g (iNewL q) ∉ Active)
    (hOldScopedInj :
      ∀ (e : F) (hePart : iOldR e ∈ OldPart)
        (heActive : f (iOldR e) ∈ Active)
        (heOutside : f (iOldR e) ∉ Seam),
        Set.InjOn f
          (OldWhole.functionClosure
            (gaifmanNeighborhood OldWhole.graph
              (componentFrom OldWhole.graph (f ⁻¹' Seam)
                (⟨iOldR e, heOutside⟩ :
                  {w : W₁ // w ∉ f ⁻¹' Seam}))))) :
    ∀ (y : W₂) (hyPart : y ∈ NewPart)
      (hyActive : g y ∈ Active)
      (hyOutside : g y ∉ Seam),
      Set.InjOn g
        (NewWhole.functionClosure
          (gaifmanNeighborhood NewWhole.graph
            (componentFrom NewWhole.graph (g ⁻¹' Seam)
              (⟨y, hyOutside⟩ :
                {w : W₂ // w ∉ g ⁻¹' Seam})))) := by
  have hNewRootSeam : ∀ r : H,
      g (iNewR (sR r)) ∈ Seam := by
    intro r
    rw [hSameE (sR r)]
    exact hOldRootSeam r
  intro y hyPart hyActive hyOutside
  rcases hNewCarrier hyPart with hQ | hE
  · obtain ⟨q, hqy⟩ := hQ
    have hQActive : g (iNewL q) ∈ Active := by
      rw [hqy]
      exact hyActive
    exact False.elim ((hNewQNoActive q) hQActive)
  · obtain ⟨e, heOldPart, hey⟩ := hE
    have hNewActive : g (iNewR e) ∈ Active := by
      rw [hey]
      exact hyActive
    have hNewOutside : g (iNewR e) ∉ Seam := by
      rw [hey]
      exact hyOutside
    have hOldActive : f (iOldR e) ∈ Active := by
      rw [← hSameE e]
      exact hNewActive
    have hOldOutside : f (iOldR e) ∉ Seam := by
      rw [← hSameE e]
      exact hNewOutside
    have hTransfer :=
      fullNativeReplacement_activeSeamBoundary_injection_transfer
        hOld hNew f g Seam hSameE hOldRootSeam hNewRootSeam
        e hOldOutside hNewOutside
        (hOldScopedInj e heOldPart hOldActive hOldOutside)
    cases hey
    exact hTransfer

end AllThoseRamseyClasses.Lifts
