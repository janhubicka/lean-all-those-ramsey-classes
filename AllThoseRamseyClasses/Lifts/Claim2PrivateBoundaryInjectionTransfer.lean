import AllThoseRamseyClasses.Lifts.FullFreeAmalgamPrivateGeneratedBoundary

/-!
# Exact active private-boundary injection survives two native Q replacements

A full functional replacement source is a genuine free amalgam of an
inserted rooted piece and an unchanged retained complement E.
For a root-containing closed context SR on the common complement,
the verified private-component source theorem yields the literal
SAME complete generated E-boundary in TWO different source diagrams:

  Bound_Old = iOldE '' T_E,   Bound_New = iNewE '' T_E.

The source carriers and inserted pieces may be totally different.
If the weak target maps agree exactly on ALL retained E source
vertices, and the OLD map was injective on its active private
generated boundary, the NEW map is injective on the corresponding
new boundary. This does not require injection of either entire
target-seam preimage, root reflection of either Q, or a new global
source injection.

This is the two-diagram, same-boundary preservation step needed
for a possible *active boundary* induction instead of demanding
global full-seam injectivity at every intermediate Claim 2 state.
The deleted context here includes the ENTIRE inserted Q side;
a separate bridge to actual target-seam components is required.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Transport injectivity of the SAME exact generated source
boundary of one retained private E-component across an arbitrary
full-functional old/new replacement pair. The only weak-target
hypothesis is exact agreement on every unchanged E source vertex. -/
theorem fullNativeReplacement_privateGeneratedBoundary_injection_transfer
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
    (SR : Set F) (hRootR : ∀ r : H, sR r ∈ SR)
    (x : {b : F // b ∉ SR})
    (f : W₁ → UT) (g : W₂ → UT)
    (hSameE : ∀ e : F, g (iNewR e) = f (iOldR e))
    (hOldInj : Set.InjOn f
      (OldWhole.functionClosure
        (gaifmanNeighborhood OldWhole.graph
          (iOldR '' componentFrom Right.graph SR x)))) :
    Set.InjOn g
      (NewWhole.functionClosure
        (gaifmanNeighborhood NewWhole.graph
          (iNewR '' componentFrom Right.graph SR x))) := by
  classical
  let TE : Set F := Right.functionClosure
    (gaifmanNeighborhood Right.graph
      (componentFrom Right.graph SR x))
  obtain ⟨hOldBoundary, hNewBoundary⟩ :=
    fullFreeAmalgam_replacement_privateBoundary_pair
      hOld hNew SR hRootR x
  intro u hu v hv huv
  have huNew : u ∈ iNewR '' TE := by
    rw [← hNewBoundary]
    exact hu
  have hvNew : v ∈ iNewR '' TE := by
    rw [← hNewBoundary]
    exact hv
  obtain ⟨e₁, he₁, heu⟩ := huNew
  obtain ⟨e₂, he₂, hev⟩ := hvNew
  have hOld₁ : iOldR e₁ ∈
      OldWhole.functionClosure
        (gaifmanNeighborhood OldWhole.graph
          (iOldR '' componentFrom Right.graph SR x)) := by
    rw [hOldBoundary]
    exact ⟨e₁, he₁, rfl⟩
  have hOld₂ : iOldR e₂ ∈
      OldWhole.functionClosure
        (gaifmanNeighborhood OldWhole.graph
          (iOldR '' componentFrom Right.graph SR x)) := by
    rw [hOldBoundary]
    exact ⟨e₂, he₂, rfl⟩
  have hOldEq : f (iOldR e₁) = f (iOldR e₂) := by
    calc
      f (iOldR e₁) = g (iNewR e₁) := (hSameE e₁).symm
      _ = g (iNewR e₂) := by simpa only [heu, hev] using huv
      _ = f (iOldR e₂) := hSameE e₂
  have hEeq : e₁ = e₂ :=
    iOldR.injective (hOldInj hOld₁ hOld₂ hOldEq)
  calc
    u = iNewR e₁ := heu.symm
    _ = iNewR e₂ := congrArg iNewR hEeq
    _ = v := hev

end AllThoseRamseyClasses.Lifts
