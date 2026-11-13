import AllThoseRamseyClasses.Lifts.Claim2PrivateRootCutComponentPersistence

/-!
# Exact source-boundary correspondence under equal retained cuts

Two arbitrary full-native free-amalgam diagrams may have different
replacement pieces and even different deleted source sets S_old
and S_new. If both cuts contain their respective glued roots and
their intersections with ONE unchanged native complement E
agree, the components of corresponding E-private vertices
and their ENTIRE function-generated source boundaries are
images of the SAME literal subset of E.

The deleted source sets need not include the entire replacement
Q and need not be function-closed. In particular they can be
different preimages of the target common root under two weak EHN
maps, even when the new map is noninjective on its full seam.

This is a path-level strengthening of the older theorem for
cuts that remove the whole Q side. It relies on the new exact
arbitrary-root-cut component/boundary transport lemma (parent
PR #1093), which is pending full Lean CI.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Two genuine native free amalgams with the same retained full
Right structure and matching deleted sets ON that Right source
have EXACTLY corresponding generated source boundaries, even
though their inserted sides and ambient source carriers differ.

Both ambient components are represented by the very SAME
Right-side component, not by independently selected witnesses. -/
theorem fullNativeReplacement_retainedCut_generatedBoundary_pair
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
    (SOld : Set W₁) (SNew : Set W₂)
    (hOldRoot : ∀ r : H, iOldR (sR r) ∈ SOld)
    (hNewRoot : ∀ r : H, iNewR (sR r) ∈ SNew)
    (hSameCutOnE : ∀ e : F,
      iOldR e ∈ SOld ↔ iNewR e ∈ SNew)
    (x : F)
    (hxOld : iOldR x ∉ SOld)
    (hxNew : iNewR x ∉ SNew) :
    ∃ T : Set F,
      OldWhole.functionClosure
        (gaifmanNeighborhood OldWhole.graph
          (componentFrom OldWhole.graph SOld
            ⟨iOldR x, hxOld⟩)) = iOldR '' T ∧
      NewWhole.functionClosure
        (gaifmanNeighborhood NewWhole.graph
          (componentFrom NewWhole.graph SNew
            ⟨iNewR x, hxNew⟩)) = iNewR '' T := by
  classical
  let SR : Set F := iOldR ⁻¹' SOld
  let xE : {e : F // e ∉ SR} := ⟨x, hxOld⟩
  let T : Set F := Right.functionClosure
    (gaifmanNeighborhood Right.graph
      (componentFrom Right.graph SR xE))
  have hSNew : iNewR ⁻¹' SNew = SR := by
    ext e
    exact (hSameCutOnE e).symm
  refine ⟨T, ?_, ?_⟩
  · exact fullFreeAmalgam_private_component_generatedBoundary_eq_image_of_rootCut
      hOld SOld hOldRoot x hxOld
  · have hNewBoundary :=
      fullFreeAmalgam_private_component_generatedBoundary_eq_image_of_rootCut
        hNew SNew hNewRoot x hxNew
    rw [hSNew] at hNewBoundary
    simpa only [T, SR, xE] using hNewBoundary

/-- Source-vertex injectivity on a generated boundary of a retained
component passes through a genuine full-native replacement whose
weak target map agrees on the entire unchanged complement.

The two deleted sets are the complete OLD and NEW target-seam
preimages, respectively; they need not be equal away from E. -/
theorem fullNativeReplacement_activeSeamBoundary_injection_transfer
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
    (Seam : Set UT)
    (hSameE : ∀ e : F, g (iNewR e) = f (iOldR e))
    (hRootSeamOld : ∀ r : H, f (iOldR (sR r)) ∈ Seam)
    (hRootSeamNew : ∀ r : H, g (iNewR (sR r)) ∈ Seam)
    (x : F)
    (hxOld : f (iOldR x) ∉ Seam)
    (hxNew : g (iNewR x) ∉ Seam)
    (hOldActiveInj : Set.InjOn f
      (OldWhole.functionClosure
        (gaifmanNeighborhood OldWhole.graph
          (componentFrom OldWhole.graph (f ⁻¹' Seam)
            (⟨iOldR x, hxOld⟩ : {w : W₁ // w ∉ f ⁻¹' Seam}))))) :
    Set.InjOn g
      (NewWhole.functionClosure
        (gaifmanNeighborhood NewWhole.graph
          (componentFrom NewWhole.graph (g ⁻¹' Seam)
            (⟨iNewR x, hxNew⟩ : {w : W₂ // w ∉ g ⁻¹' Seam})))) := by
  classical
  have hSameCut : ∀ e : F,
      iOldR e ∈ (f ⁻¹' Seam) ↔ iNewR e ∈ (g ⁻¹' Seam) := by
    intro e
    change f (iOldR e) ∈ Seam ↔ g (iNewR e) ∈ Seam
    rw [hSameE e]
  obtain ⟨T, hOldBoundary, hNewBoundary⟩ :=
    fullNativeReplacement_retainedCut_generatedBoundary_pair
      hOld hNew (f ⁻¹' Seam) (g ⁻¹' Seam)
      hRootSeamOld hRootSeamNew hSameCut x hxOld hxNew
  intro u hu v hv huv
  rw [hNewBoundary] at hu hv
  obtain ⟨e₁, he₁, heu⟩ := hu
  obtain ⟨e₂, he₂, hev⟩ := hv
  have hOldU : iOldR e₁ ∈
      OldWhole.functionClosure
        (gaifmanNeighborhood OldWhole.graph
          (componentFrom OldWhole.graph (f ⁻¹' Seam)
            (⟨iOldR x, hxOld⟩ : {w : W₁ // w ∉ f ⁻¹' Seam}))) := by
    rw [hOldBoundary]
    exact ⟨e₁, he₁, rfl⟩
  have hOldV : iOldR e₂ ∈
      OldWhole.functionClosure
        (gaifmanNeighborhood OldWhole.graph
          (componentFrom OldWhole.graph (f ⁻¹' Seam)
            (⟨iOldR x, hxOld⟩ : {w : W₁ // w ∉ f ⁻¹' Seam}))) := by
    rw [hOldBoundary]
    exact ⟨e₂, he₂, rfl⟩
  have hOldTargetEq : f (iOldR e₁) = f (iOldR e₂) := by
    calc
      f (iOldR e₁) = g (iNewR e₁) := (hSameE e₁).symm
      _ = g (iNewR e₂) := by simpa only [heu, hev] using huv
      _ = f (iOldR e₂) := hSameE e₂
  have hSourceEq : e₁ = e₂ :=
    iOldR.injective (hOldActiveInj hOldU hOldV hOldTargetEq)
  calc
    u = iNewR e₁ := heu.symm
    _ = iNewR e₂ := congrArg iNewR hSourceEq
    _ = v := hev

/-- A full-native source flip that introduces NO vertices with images
in an arbitrary active target region transfers boundary injectivity
for EVERY surviving active source vertex, not just one chosen
component. The old and new weak maps may differ completely on
the inserted root-extension pieces, including new root collisions.

This is the one-step invariant needed if the active target region
is the original B-exclusive side of the 2019 full amalgam and
the inserted replacement Q maps into the opposite A/Left side. -/
theorem fullNativeReplacement_allActiveSeamBoundaries_injection_transfer
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
    (hSameE : ∀ e : F, g (iNewR e) = f (iOldR e))
    (hRootSeamOld : ∀ r : H, f (iOldR (sR r)) ∈ Seam)
    (hRootSeamNew : ∀ r : H, g (iNewR (sR r)) ∈ Seam)
    (hNoNewActive : ∀ q : E₂, g (iNewL q) ∉ Active)
    (hOldActiveInj :
      ∀ (e : F) (heActive : f (iOldR e) ∈ Active)
        (heOutside : f (iOldR e) ∉ Seam),
        Set.InjOn f
          (OldWhole.functionClosure
            (gaifmanNeighborhood OldWhole.graph
              (componentFrom OldWhole.graph (f ⁻¹' Seam)
                (⟨iOldR e, heOutside⟩ :
                  {w : W₁ // w ∉ f ⁻¹' Seam}))))) :
    ∀ (y : W₂) (hyActive : g y ∈ Active)
      (hyOutside : g y ∉ Seam),
      Set.InjOn g
        (NewWhole.functionClosure
          (gaifmanNeighborhood NewWhole.graph
            (componentFrom NewWhole.graph (g ⁻¹' Seam)
              (⟨y, hyOutside⟩ :
                {w : W₂ // w ∉ g ⁻¹' Seam})))) := by
  intro y hyActive hyOutside
  rcases hNew.covers y with ⟨q, hq⟩ | ⟨e, he⟩
  · have hForbiddenActive : g (iNewL q) ∈ Active := by
      rw [← hq]
      exact hyActive
    exact False.elim (hNoNewActive q hForbiddenActive)
  · have hEActive : g (iNewR e) ∈ Active := by
      rw [← he]
      exact hyActive
    have hEOutside : g (iNewR e) ∉ Seam := by
      rw [← he]
      exact hyOutside
    have hOldActive : f (iOldR e) ∈ Active := by
      rw [← hSameE e]
      exact hEActive
    have hOldOutside : f (iOldR e) ∉ Seam := by
      rw [← hSameE e]
      exact hEOutside
    have hTransferred :=
      fullNativeReplacement_activeSeamBoundary_injection_transfer
        hOld hNew f g Seam
        hSameE hRootSeamOld hRootSeamNew
        e hOldOutside hEOutside
        (hOldActiveInj e hOldActive hOldOutside)
    cases he
    exact hTransferred

end AllThoseRamseyClasses.Lifts
