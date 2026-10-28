import AllThoseRamseyClasses.Lifts.FullFreeAmalgamPrivateGaifman

/-!
# Exact components outside a transported full functional context

Let Whole be a genuine FULL native functional free amalgam
Left +_Root Right. A right subset SR contains the entire
common root. The contextual source vertex set
  K = iLeft(Left) ∪ iRight(SR)
contains the new piece and the part of the old complement
retained inside the old outer source piece.

The verified exact exterior equivalence identifies the entire
complement of K with Right minus SR; its verified adjacency
and path theorem reflects every Gaifman edge and path.

We now prove equality of the COMPLETE connected component
subsets, considered as vertex sets of the full source:
  component(Whole\K, iRight(x))
    = iRight[component(Right\SR, x)].

This is stronger than bijectivity of outside vertices or
correspondence of chosen paths. The result can be compared
across TWO different full free-amalgam replacement sources
over one unchanged right complement, showing literal
preservation of the exterior components under a contextual
B-only flip.

The theorem uses only FULL source embeddings; a forbidden EHN
weak target map may be noninjective. It does NOT establish that
the transported INSIDE context is a new geometric minimal-cut
piece or that its all-test incompatibility profile is unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F W : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E}
variable {Right : Structure L F}
variable {Whole : Structure L W}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- The full native Gaifman component outside a root-containing
whole context is EXACTLY the image of the original right-side
component. The equality includes all surviving source vertices,
not merely their images in a weak target structure. -/
theorem fullFreeAmalgam_rightOutsideContext_component_eq
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (SR : Set F) (hRootR : ∀ r : H, sR r ∈ SR)
    (x : {b : F // b ∉ SR}) :
    componentFrom Whole.graph
      (iL '' (Set.univ : Set E) ∪ iR '' SR)
      ((fullFreeAmalgam_rightOutsideContextEquiv
        hFree SR hRootR) x) =
    iR '' componentFrom Right.graph SR x := by
  let K : Set W := iL '' (Set.univ : Set E) ∪ iR '' SR
  let e := fullFreeAmalgam_rightOutsideContextEquiv
    hFree SR hRootR
  apply Set.Subset.antisymm
  · intro z hz
    let w : {z : W // z ∉ K} := ⟨z, hz.1⟩
    have hPath :
        ReachOutside Right.graph SR x (e.symm w) := by
      apply (fullFreeAmalgam_rightOutsideContext_reach_iff
        hFree SR hRootR x (e.symm w)).mp
      have he : e (e.symm w) = w := e.apply_symm_apply w
      simpa only [he] using hz.2
    have hValue : iR (e.symm w).1 = z := by
      have he := congrArg Subtype.val (e.apply_symm_apply w)
      change iR (e.symm w).1 = z at he
      exact he
    exact ⟨(e.symm w).1, ⟨(e.symm w).2, hPath⟩, hValue⟩
  · rintro z ⟨b, hb, rfl⟩
    let b' : {b : F // b ∉ SR} := ⟨b, hb.1⟩
    have hPath :
        ReachOutside Whole.graph K (e x) (e b') :=
      (fullFreeAmalgam_rightOutsideContext_reach_iff
        hFree SR hRootR x b').mpr hb.2
    change iR b ∈ componentFrom Whole.graph K (e x)
    exact ⟨(e b').2, hPath⟩

/-- Every exterior component is identical, through its right-side
coordinates, in TWO actual native source amalgams with different
left replacement pieces and one literal full retained right side.

In particular the components under consideration do not acquire
fresh left-private vertices, even with arbitrary partial function
incidences and constants in the source language. -/
theorem fullFreeAmalgam_replacement_privateComponent_pair
    {H E₁ E₂ F W₁ W₂ : Type v}
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
    (SR : Set F) (hRootR : ∀ r : H, sR r ∈ SR)
    (x : {b : F // b ∉ SR}) :
    (componentFrom OldWhole.graph
       (iOldL '' (Set.univ : Set E₁) ∪ iOldR '' SR)
       ((fullFreeAmalgam_rightOutsideContextEquiv
         hOld SR hRootR) x) =
      iOldR '' componentFrom Right.graph SR x) ∧
    (componentFrom NewWhole.graph
       (iNewL '' (Set.univ : Set E₂) ∪ iNewR '' SR)
       ((fullFreeAmalgam_rightOutsideContextEquiv
         hNew SR hRootR) x) =
      iNewR '' componentFrom Right.graph SR x) := by
  exact ⟨
    fullFreeAmalgam_rightOutsideContext_component_eq
      hOld SR hRootR x,
    fullFreeAmalgam_rightOutsideContext_component_eq
      hNew SR hRootR x⟩

end AllThoseRamseyClasses.Lifts
