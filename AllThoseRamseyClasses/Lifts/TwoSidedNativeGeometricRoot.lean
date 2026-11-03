import AllThoseRamseyClasses.Lifts.InsertedPrivateComponentBoundary
import AllThoseRamseyClasses.Lifts.WeakMinimalGeometricChart

/-!
# Two exact private component boundaries produce a genuine new geometric piece

The canonical 2019 source flip produces a FULL functional free
amalgam of its inserted selected extension and unchanged native
complement. An abstract common closed root does not automatically
remain minimal. What suffices is to show that the COMPLETE
function-generated external boundaries of one private component
on EACH side equal the complete common root on that side.

The inserted-side component equation is now supplied by the
verified right-side exterior result and the swapped diagram.
The unchanged complement's opposite component is handled by the
original right-side result. Exact overlap identifies their
whole root images, the private left component cannot intersect
the right component, and the verified converse minimal-separator
theorem proves the common cut is a MINIMAL CLOSED separator.

For a FINITE new source, the existing chart-construction theorem
then produces a literal GeometricFunctionalPieceData with EXACT
complete closed root and selected component representatives.
No original function fibre, graph tuple, or closed-root coordinate
is silently discarded.

The input component-boundary equations still have to be proved
for the particular replacement Q and retained original complement.
The theorem does not assert that any arbitrary rooted extension
satisfies them, nor an unrestricted Claim 2.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Source Gaifman components are invariant under a change of
the cut by literal set equality, provided their chosen vertices
agree. The dependent surviving-vertex subtype is transported
as a whole, rather than incorrectly rewriting inside it. -/
private theorem componentFrom_congr_of_equalCuts
    {W : Type v} (Whole : Structure L W)
    {S T : Set W} (hST : S = T)
    (x : {w : W // w ∉ S})
    (y : {w : W // w ∉ T})
    (hxy : x.1 = y.1) :
    componentFrom Whole.graph S x = componentFrom Whole.graph T y := by
  cases hST
  have hEq : x = y := Subtype.ext hxy
  cases hEq
  rfl

/-- A finite whole-source FULL functional amalgam of two rooted
extensions has a GENUINE minimal-separator geometric piece with
the entire shared native root provided each selected private
side component has whole generated boundary equal to the root.

This is a full functional (not graph-only) strengthening of
the existing opposite-boundary criterion, symmetrically
treating the two distinguished components. -/
theorem fullFreeAmalgam_twoPrivateBoundaries_hasGeometricPiece
    {H E B W : Type v} [Finite W]
    {Root : Structure L H}
    {Inner : Structure L E}
    {Complement : Structure L B}
    {Whole : Structure L W}
    {sInner : Structure.Embedding Root Inner}
    {sComp : Structure.Embedding Root Complement}
    {iInner : Structure.Embedding Inner Whole}
    {iComp : Structure.Embedding Complement Whole}
    (hFree : Structure.IsFreeAmalgam sInner sComp iInner iComp)
    (dInner : {e : E // e ∉ Set.range sInner})
    (dComp : {b : B // b ∉ Set.range sComp})
    (hInnerBoundary :
      Inner.functionClosure
        (gaifmanNeighborhood Inner.graph
          (componentFrom Inner.graph (Set.range sInner) dInner)) =
        Set.range sInner)
    (hCompBoundary :
      Complement.functionClosure
        (gaifmanNeighborhood Complement.graph
          (componentFrom Complement.graph (Set.range sComp) dComp)) =
        Set.range sComp) :
    ∃ (m : ℕ) (d : GeometricFunctionalPieceData Whole m),
      Set.range d.roots = iComp '' Set.range sComp ∧
      d.left.1 = iInner dInner.1 ∧
      d.right.1 = iComp dComp.1 := by
  let Rinner : Set W := iInner '' Set.range sInner
  let Rcomp : Set W := iComp '' Set.range sComp
  have hCommon (r : H) :
      iInner (sInner r) = iComp (sComp r) :=
    (hFree.overlap (sInner r) (sComp r)).mpr ⟨r, rfl, rfl⟩
  have hRoots : Rinner = Rcomp := by
    ext w
    constructor
    · rintro ⟨e, ⟨r, hr⟩, he⟩
      refine ⟨sComp r, ⟨r, rfl⟩, ?_⟩
      calc
        iComp (sComp r) = iInner (sInner r) := (hCommon r).symm
        _ = iInner e := congrArg iInner hr
        _ = w := he
    · rintro ⟨b, ⟨r, hr⟩, hb⟩
      refine ⟨sInner r, ⟨r, rfl⟩, ?_⟩
      calc
        iInner (sInner r) = iComp (sComp r) := hCommon r
        _ = iComp b := congrArg iComp hr
        _ = w := hb
  let xInnerOrig : {w : W // w ∉ Rinner} :=
    fullFunctionalEmbedding_outsideCut iInner
      (Set.range sInner) dInner
  let xInner : {w : W // w ∉ Rcomp} :=
    ⟨iInner dInner.1, by
      rw [← hRoots]
      exact xInnerOrig.2⟩
  let xComp : {w : W // w ∉ Rcomp} :=
    fullFunctionalEmbedding_outsideCut iComp
      (Set.range sComp) dComp
  have hCompCongruence :
      componentFrom Whole.graph Rcomp xInner =
        componentFrom Whole.graph Rinner xInnerOrig :=
    componentFrom_congr_of_equalCuts Whole hRoots.symm
      xInner xInnerOrig rfl
  have hInserted :=
    fullFreeAmalgam_insertedPrivateComponent_exactBoundary
      hFree dInner hInnerBoundary
  have hExterior :=
    fullFreeAmalgam_exteriorComponent_preserved_at_oldRoot
      hFree (Set.range sComp) dComp
      (by intro b hb; exact hb.1) hCompBoundary
  have hInnerBoundaryWhole :
      Whole.functionClosure
        (gaifmanNeighborhood Whole.graph
          (componentFrom Whole.graph Rcomp xInner)) = Rcomp := by
    rw [hCompCongruence, hInserted.1]
    exact hInserted.2.trans hRoots
  have hCompBoundaryWhole :
      Whole.functionClosure
        (gaifmanNeighborhood Whole.graph
          (componentFrom Whole.graph Rcomp xComp)) = Rcomp := by
    rw [hExterior.1]
    exact hExterior.2
  have hClosedRoot : Whole.IsClosed Rcomp :=
    functionalEmbedding_image_closed
      Complement Whole iComp (Set.range sComp)
      sComp.range_isClosed
  have hInnerPrivateNotComp :
      iInner dInner.1 ∉ Set.range iComp := by
    rintro ⟨b, hb⟩
    obtain ⟨r, hrInner, _⟩ :=
      (hFree.overlap dInner.1 b).mp hb.symm
    exact dInner.2 ⟨r, hrInner.symm⟩
  have hSeparated :
      ¬ ReachOutside Whole.graph Rcomp xInner xComp := by
    intro hReach
    have hReverse :
        ReachOutside Whole.graph Rcomp xComp xInner :=
      reachOutside_symm Whole.graph Rcomp hReach
    have hInComp :
        xInner.1 ∈ componentFrom Whole.graph Rcomp xComp :=
      ⟨xInner.2, hReverse⟩
    rw [hExterior.1] at hInComp
    obtain ⟨b, _, hb⟩ := hInComp
    exact hInnerPrivateNotComp ⟨b, hb⟩
  have hMinimal : IsMinimalClosedSeparator Whole Rcomp
      xInner xComp :=
    minimalClosedSeparator_of_bothBoundaries_eq
      Whole Rcomp hClosedRoot xInner xComp hSeparated
      hInnerBoundaryWhole hCompBoundaryWhole
  obtain ⟨m, d, hRoot, hLeft, hRight⟩ :=
    finiteMinimalClosedSeparator_toGeometricChart
      Whole Rcomp xInner xComp hMinimal
  exact ⟨m, d, hRoot, hLeft, hRight⟩

end AllThoseRamseyClasses.Lifts
