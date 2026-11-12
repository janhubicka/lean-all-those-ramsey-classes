import AllThoseRamseyClasses.Lifts.FullFreeAmalgamPrivateGeneratedBoundary
import AllThoseRamseyClasses.Lifts.SeparatorPaths

/-!
# Private complement components persist under ANY root-containing source cut

Let Whole = Left +_Root Right be a genuine FULL native functional
free amalgam. Delete any arbitrary source set S which contains
the complete embedded shared Root: S need NOT contain the entire
Left source side or be function-closed.

Every connected component of Whole minus S that begins at
a RIGHT-private vertex stays entirely in the RIGHT source
embedding, and even avoids the Right-preimage SR of S.
Otherwise a path exiting the private right set would have to
cross its full external Gaifman neighbourhood. The verified
full-native private-side neighbourhood theorem shows that all
such exit vertices lie in embedded SR, already deleted by S.

Moreover, the ENTIRE function-generated neighbourhood boundary
of that component also lies in the Right embedding, using the
verified full-embedding generated-boundary equality, with no
assumptions on the other (inserted) source side.

This is the path-transport bridge from a context that removes the
entire inserted Q to an arbitrary target-seam deleted cut
(which typically removes only its root, not the rest of Q).
It does not require weak EHN maps, forbidden-family minimality,
root reflection, finiteness, or any target-image quotient.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- A true source Gaifman component beginning on the retained
Right/Complement side cannot cross into the inserted Left side
along paths that avoid an arbitrary S containing the full
source gluing root. -/
theorem fullFreeAmalgam_private_component_stays_right_of_rootCut
    {H E F W : Type v}
    {Root : Structure L H}
    {Left : Structure L E}
    {Right : Structure L F}
    {Whole : Structure L W}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (S : Set W)
    (hRootS : ∀ r : H, iR (sR r) ∈ S)
    (xR : F) (hxOutS : iR xR ∉ S) :
    componentFrom Whole.graph S ⟨iR xR, hxOutS⟩ ⊆
      iR '' {b : F | iR b ∉ S} := by
  let SR : Set F := iR ⁻¹' S
  let Private : Set F := {b | b ∉ SR}
  let C : Set W := iR '' Private
  have hRootSR : ∀ r : H, sR r ∈ SR := by
    intro r
    exact hRootS r
  have hBoundaryEq :
      gaifmanNeighborhood Whole.graph C =
        iR '' gaifmanNeighborhood Right.graph Private :=
    fullFreeAmalgam_rightPrivate_neighborhood_eq_image
      hFree SR Private hRootSR (fun _ he => he)
  have hBoundaryInS :
      gaifmanNeighborhood Whole.graph C ⊆ S := by
    intro w hw
    rw [hBoundaryEq] at hw
    obtain ⟨b, hbBoundary, hbMap⟩ := hw
    have hbSR : b ∈ SR := by
      by_contra hbPrivate
      exact hbBoundary.1 hbPrivate
    have hbS : iR b ∈ S := hbSR
    exact hbMap ▸ hbS
  have hxC : iR xR ∈ C := by
    refine ⟨xR, ?_, rfl⟩
    exact hxOutS
  intro w hw
  exact reachOutside_stays_in_avoid_boundary
    Whole.graph S C ⟨iR xR, hxOutS⟩
    hxC hBoundaryInS hw.2

/-- The COMPLETE generated external source boundary of the same
S-avoiding retained-private component also lies in the
retained Right embedding, even if the inserted Q has
nonroot source vertices mapping into the target common seam.

No source map or closure hypothesis on S is needed. -/
theorem fullFreeAmalgam_private_component_generatedBoundary_in_right_of_rootCut
    {H E F W : Type v}
    {Root : Structure L H}
    {Left : Structure L E}
    {Right : Structure L F}
    {Whole : Structure L W}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (S : Set W)
    (hRootS : ∀ r : H, iR (sR r) ∈ S)
    (xR : F) (hxOutS : iR xR ∉ S) :
    Whole.functionClosure
      (gaifmanNeighborhood Whole.graph
        (componentFrom Whole.graph S ⟨iR xR, hxOutS⟩)) ⊆
      Set.range iR := by
  classical
  let SR : Set F := iR ⁻¹' S
  let Private : Set F := {b | b ∉ SR}
  let C : Set W :=
    componentFrom Whole.graph S ⟨iR xR, hxOutS⟩
  let CE : Set F := iR ⁻¹' C
  have hCinside : C ⊆ iR '' Private :=
    fullFreeAmalgam_private_component_stays_right_of_rootCut
      hFree S hRootS xR hxOutS
  have hCimage : C = iR '' CE := by
    apply Set.Subset.antisymm
    · intro w hw
      obtain ⟨b, _hbPrivate, hbMap⟩ := hCinside hw
      refine ⟨b, ?_, hbMap⟩
      simpa only [hbMap] using hw
    · rintro w ⟨b, hbC, hbMap⟩
      exact hbMap ▸ hbC
  have hCEprivate : CE ⊆ {b : F | b ∉ SR} := by
    intro b hb
    exact hb.1
  have hRootSR : ∀ r : H, sR r ∈ SR := by
    intro r
    exact hRootS r
  have hBoundaryEq :
      Whole.functionClosure
        (gaifmanNeighborhood Whole.graph C) =
      iR '' (Right.functionClosure
        (gaifmanNeighborhood Right.graph CE)) := by
    rw [hCimage]
    exact fullFreeAmalgam_private_generatedBoundary_eq_image
      hFree SR CE hRootSR hCEprivate
  intro w hw
  change w ∈ Whole.functionClosure
    (gaifmanNeighborhood Whole.graph C) at hw
  rw [hBoundaryEq] at hw
  obtain ⟨b, _hb, hbMap⟩ := hw
  exact ⟨b, hbMap⟩

/-- Exact source-component equality for an arbitrary deleted vertex set S
containing the entire glued native root. No closedness of S and no
weak target-map injectivity is required. -/
theorem fullFreeAmalgam_private_component_eq_image_of_rootCut
    {H E F W : Type v}
    {Root : Structure L H}
    {Left : Structure L E}
    {Right : Structure L F}
    {Whole : Structure L W}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (S : Set W)
    (hRootS : ∀ r : H, iR (sR r) ∈ S)
    (xR : F) (hxOutS : iR xR ∉ S) :
    componentFrom Whole.graph S ⟨iR xR, hxOutS⟩ =
      iR '' componentFrom Right.graph (iR ⁻¹' S)
        (⟨xR, hxOutS⟩ : {b : F // b ∉ iR ⁻¹' S}) := by
  classical
  let SR : Set F := iR ⁻¹' S
  let xE : {b : F // b ∉ SR} := ⟨xR, hxOutS⟩
  let xW : {w : W // w ∉ S} := ⟨iR xR, hxOutS⟩
  let CE : Set F := componentFrom Right.graph SR xE
  let C : Set W := iR '' CE
  have hRootSR : ∀ r : H, sR r ∈ SR := hRootS
  have hCEprivate : CE ⊆ {e : F | e ∉ SR} := by
    intro e he
    exact he.1
  have hNeighborhood :
      gaifmanNeighborhood Whole.graph C =
      iR '' gaifmanNeighborhood Right.graph CE :=
    fullFreeAmalgam_rightPrivate_neighborhood_eq_image
      hFree SR CE hRootSR hCEprivate
  have hNeighborhoodInside : gaifmanNeighborhood Whole.graph C ⊆ S := by
    intro w hw
    rw [hNeighborhood] at hw
    obtain ⟨e, he, hew⟩ := hw
    have heSR : e ∈ SR :=
      functionalNeighborhood_component_subset_cut Right SR xE he
    rw [← hew]
    exact heSR
  have hxC : iR xR ∈ C := by
    exact ⟨xR, componentFrom_root Right.graph SR xE, rfl⟩
  have hWholeInside :
      componentFrom Whole.graph S xW ⊆ C := by
    intro w hw
    exact reachOutside_stays_in_avoid_boundary
      Whole.graph S C xW hxC hNeighborhoodInside hw.2
  let mapOutside : {e : F // e ∉ SR} → {w : W // w ∉ S} :=
    fun e => ⟨iR e.1, e.2⟩
  have hEdge : ∀ {a b : {e : F // e ∉ SR}},
      outsideAdjacency Right.graph SR a b →
      outsideAdjacency Whole.graph S (mapOutside a) (mapOutside b) := by
    intro a b hab
    have haPrivate : a.1 ∉ Set.range sR := by
      rintro ⟨r, hr⟩
      exact a.2 (hr ▸ hRootSR r)
    exact (fullFreeAmalgam_rightPrivate_gaifmanAdjacent_iff
      hFree a.1 b.1 haPrivate).mpr hab
  have hReach : ∀ {a b : {e : F // e ∉ SR}},
      ReachOutside Right.graph SR a b →
      ReachOutside Whole.graph S (mapOutside a) (mapOutside b) := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail hpath hedge ih =>
        exact ih.tail (hEdge hedge)
  have hImageInside :
      C ⊆ componentFrom Whole.graph S xW := by
    rintro w ⟨e, he, hew⟩
    have heWhole : iR e ∈ componentFrom Whole.graph S xW := by
      refine ⟨he.1, ?_⟩
      exact hReach he.2
    exact hew ▸ heWhole
  exact Set.Subset.antisymm hWholeInside hImageInside

/-- Exact transport of the ENTIRE native function-generated boundary
for a private component after an arbitrary common-root-containing cut.
The inserted left source cannot add any extra boundary vertices. -/
theorem fullFreeAmalgam_private_component_generatedBoundary_eq_image_of_rootCut
    {H E F W : Type v}
    {Root : Structure L H}
    {Left : Structure L E}
    {Right : Structure L F}
    {Whole : Structure L W}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (S : Set W)
    (hRootS : ∀ r : H, iR (sR r) ∈ S)
    (xR : F) (hxOutS : iR xR ∉ S) :
    Whole.functionClosure
      (gaifmanNeighborhood Whole.graph
        (componentFrom Whole.graph S ⟨iR xR, hxOutS⟩)) =
      iR '' (Right.functionClosure
        (gaifmanNeighborhood Right.graph
          (componentFrom Right.graph (iR ⁻¹' S)
            (⟨xR, hxOutS⟩ : {b : F // b ∉ iR ⁻¹' S})))) := by
  let SR : Set F := iR ⁻¹' S
  let xE : {b : F // b ∉ SR} := ⟨xR, hxOutS⟩
  let CE : Set F := componentFrom Right.graph SR xE
  have hRootSR : ∀ r : H, sR r ∈ SR := hRootS
  have hCEprivate : CE ⊆ {e : F | e ∉ SR} := by
    intro e he
    exact he.1
  rw [fullFreeAmalgam_private_component_eq_image_of_rootCut
    hFree S hRootS xR hxOutS]
  exact fullFreeAmalgam_private_generatedBoundary_eq_image
    hFree SR CE hRootSR hCEprivate

end AllThoseRamseyClasses.Lifts
