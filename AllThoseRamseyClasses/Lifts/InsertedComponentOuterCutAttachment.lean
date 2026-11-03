import AllThoseRamseyClasses.Lifts.InsertedPrivateComponentBoundary
import AllThoseRamseyClasses.Lifts.InnerComponentOuterCutTransport
import AllThoseRamseyClasses.Lifts.GeneratedSubcomponentBoundaryLocalization
import AllThoseRamseyClasses.Lifts.FullComplementClosedOuterRoot

/-!
# Genuine inserted private component across an arbitrary old closed cut

Let New be a literal FULL functional free amalgam of a selected
replacement piece Q and the unchanged complement B over their
complete shared root U. The older closed root T lives in B and
need NOT be comparable with U. Assume the selected Q-private
component D_Q has its ENTIRE generated native boundary equal to U.
(Track A's selected-Q witness theorem supplies this eventually.)

The exact full-amalgam component theorem identifies its image D
as a genuine component of New minus U and preserves its
function-generated boundary U. D cannot meet T: any intersection
of a left-private vertex with the complete right side would lie
in the common full root, contradiction.

The verified incomparable-cut component theorem now gives ONE
actual New minus T component C' containing D. Generated-boundary
attachment gives U minus T subset C', while subcomponent
boundary localization gives U intersect T subset Cl(N(C')).

This packages BOTH previously conditional inputs needed by
the original nested Claim 2 restoration into an actual
SOURCE-side consequence of the selected Q root-boundary theorem.
No function arity restriction, target HE injectivity, or
inclusion between the two cuts is assumed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- A genuine private inserted component of a FULL native
functional source flip survives any older function-closed
cut in the unchanged complement, and its COMPLETE shared
root attaches on both sides of that cut.

The old/new whole-source structure can have arbitrarily
high-arity native relations and set-valued partial functions.
The only genuine geometric input is the internal complete
generated root boundary of Q; it is NOT assumed that T
or U is a subset of the other. -/
theorem fullFreeAmalgam_insertedComponent_outerCut_attaches
    {H E B W : Type v}
    {Root : Structure L H}
    {Inner : Structure L E}
    {Complement : Structure L B}
    {Whole : Structure L W}
    {sInner : Structure.Embedding Root Inner}
    {sComp : Structure.Embedding Root Complement}
    {iInner : Structure.Embedding Inner Whole}
    {iComp : Structure.Embedding Complement Whole}
    (hFree : Structure.IsFreeAmalgam sInner sComp iInner iComp)
    (T : Set B) (hTclosed : Complement.IsClosed T)
    (d : {e : E // e ∉ Set.range sInner})
    (hInnerBoundary :
      Inner.functionClosure
        (gaifmanNeighborhood Inner.graph
          (componentFrom Inner.graph (Set.range sInner) d)) =
        Set.range sInner) :
    ∃ x : {w : W // w ∉ iComp '' T},
      x.1 = iInner d.1 ∧
      iInner '' componentFrom Inner.graph (Set.range sInner) d ⊆
        componentFrom Whole.graph (iComp '' T) x ∧
      (∀ r : H, sComp r ∉ T →
        iComp (sComp r) ∈
          componentFrom Whole.graph (iComp '' T) x) ∧
      (∀ r : H, sComp r ∈ T →
        iComp (sComp r) ∈ Whole.functionClosure
          (gaifmanNeighborhood Whole.graph
            (componentFrom Whole.graph (iComp '' T) x))) := by
  let U : Set W := iInner '' Set.range sInner
  let inner : {w : W // w ∉ U} :=
    fullFunctionalEmbedding_outsideCut iInner
      (Set.range sInner) d
  have hInserted :=
    fullFreeAmalgam_insertedPrivateComponent_exactBoundary
      hFree d hInnerBoundary
  have hWholeBoundary :
      Whole.functionClosure
        (gaifmanNeighborhood Whole.graph
          (componentFrom Whole.graph U inner)) = U := by
    rw [hInserted.1]
    exact hInserted.2
  have hTclosedWhole : Whole.IsClosed (iComp '' T) :=
    functionalEmbedding_image_closed
      Complement Whole iComp T hTclosed
  have hDisjoint :
      Disjoint
        (componentFrom Whole.graph U inner)
        (iComp '' T) := by
    apply Set.disjoint_left.mpr
    intro z hz ⟨b, hb, hzb⟩
    rw [hInserted.1] at hz
    obtain ⟨e, he, hze⟩ := hz
    have heComp : iInner e = iComp b := hze.trans hzb.symm
    obtain ⟨r, hrInner, _hrComp⟩ :=
      (hFree.overlap e b).mp heComp
    exact he.1 ⟨r, hrInner.symm⟩
  obtain ⟨x, hx, hInside⟩ :=
    innerComponent_subset_outerComponent_of_disjoint
      Whole U (iComp '' T) inner hDisjoint
  have hRootOutside :
      U \ (iComp '' T) ⊆
        componentFrom Whole.graph (iComp '' T) x :=
    generatedInnerRoot_outsideClosedOuterCut_attaches
      Whole (iComp '' T) hTclosedWhole x
      (componentFrom Whole.graph U inner) U
      hInside hWholeBoundary
  have hRootInside :
      U ∩ (iComp '' T) ⊆
        Whole.functionClosure
          (gaifmanNeighborhood Whole.graph
            (componentFrom Whole.graph (iComp '' T) x)) := by
    intro z hz
    have hzGenerated :
        z ∈ Whole.functionClosure
          (gaifmanNeighborhood Whole.graph
            (componentFrom Whole.graph U inner)) := by
      rw [hWholeBoundary]
      exact hz.1
    exact generatedSubcomponentBoundary_inter_cut_subset_componentBoundary
      Whole (iComp '' T) hTclosedWhole x
      (componentFrom Whole.graph U inner) hInside
      z hzGenerated hz.2
  have hRootCoincide (r : H) :
      iInner (sInner r) = iComp (sComp r) :=
    (hFree.overlap (sInner r) (sComp r)).mpr
      ⟨r, rfl, rfl⟩
  have hRootInU (r : H) : iComp (sComp r) ∈ U :=
    ⟨sInner r, ⟨r, rfl⟩, hRootCoincide r⟩
  refine ⟨x, hx, ?_, ?_, ?_⟩
  · rw [hInserted.1] at hInside
    exact hInside
  · intro r hrT
    have hNotT : iComp (sComp r) ∉ iComp '' T := by
      rintro ⟨b, hb, hbeq⟩
      have hr : b = sComp r := iComp.injective hbeq
      exact hrT (hr ▸ hb)
    exact hRootOutside ⟨hRootInU r, hNotT⟩
  · intro r hrT
    have hInT : iComp (sComp r) ∈ iComp '' T :=
      ⟨sComp r, hrT, rfl⟩
    exact hRootInside ⟨hRootInU r, hInT⟩

end AllThoseRamseyClasses.Lifts
