import AllThoseRamseyClasses.Lifts.ComponentBoundaryPieceCriterion
import AllThoseRamseyClasses.Lifts.GeometricProperSubpiece

/-!
# A boundary-partner component inside a geometric piece gives a PROPER sub-piece

The printed Section 3 Claim 2 needs genuine source-attached
proper sub-pieces, not only smaller source Gaifman components.

Let P = R ∪ C be an actual geometric piece of an original
functional source, let R ⊆ S be any larger source cut, and
let B be a complete component of Source minus S whose
distinguished vertex belongs to C.

Its entire external Gaifman neighbourhood lies inside P:
a neighbour outside the original root R can only remain
in C. Because P is NATIVE function-closed, the whole
generated closure T=Cl(N(B)) also lies inside P. This
is true even when some closure vertices are not immediate
graph neighbours.

Now assume that T has an ACTUAL boundary partner in the
sense of the verified exact criterion (#576), so that
T is a minimal closed separator and B is the selected
component of a genuine new geometric piece Q.
If the old component C contains a vertex a outside
both S and B, then the full vertex set T ∪ B of Q
lies inside P, while a belongs to P but not Q.
Consequently Q is a LITERAL PROPER sub-piece of P
in the paper's sense, including its entire closed root.

This source-geometric theorem does NOT assume target-map
injectivity or a canonical lift. It does not prove that
the required boundary partner exists in the published
multicomponent case, nor does it construct the later
forbidden-source EHN flip.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The full functional closure of the external neighbourhood
of an S-component B contained in the selected component of
a genuine piece P is contained in P's WHOLE closed vertex
set, including its original separator root.

No closedness of S is required in this purely local result:
only R⊆S and exact Gaifman component reachability are used. -/
theorem componentBoundaryClosure_inside_geometricPiece
    (A : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData A n)
    (S : Set V)
    (hRS : Set.range d.roots ⊆ S)
    (x : {v : V // v ∉ S})
    (hxOld : x.1 ∈
      functionalComponentFrom A (Set.range d.roots) d.left) :
    A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph S x)) ⊆
        geometricPieceVertices A d := by
  let R : Set V := Set.range d.roots
  let C : Set V := componentFrom A.graph R d.left
  let B : Set V := componentFrom A.graph S x
  have hxReach : ReachOutside A.graph R
      d.left (outsideCutMap hRS x) := hxOld.2
  have hBsubsetC : B ⊆ C := by
    intro z hzB
    have hzR :=
      componentFrom_subset_of_cut_subset A.graph hRS x hzB
    exact ⟨hzR.1, hxReach.trans hzR.2⟩
  have hNeighbour : gaifmanNeighborhood A.graph B ⊆ R ∪ C := by
    intro z hz
    by_cases hzR : z ∈ R
    · exact Or.inl hzR
    · obtain ⟨_hzNotB, b, hbB, hbz⟩ := hz
      exact Or.inr
        (componentFrom_step A.graph R d.left
          (hBsubsetC hbB) hzR hbz)
  have hPieceClosed : A.IsClosed (R ∪ C) :=
    functionalComponentUnion_isClosed
      A R d.minimal.1 d.left
  intro z hz
  exact hz (R ∪ C) hPieceClosed hNeighbour

/-- A REAL boundary partner of an S-component B contained
in an old selected component C yields a new geometric source
piece Q with strictly smaller FULL vertex set.

The extra old vertex a is required to survive S and to lie
outside B. In a target free-amalgam application, a may be
left-exclusive and B right-exclusive: the verified
monochromatic source-component lemma supplies this separation.

No claim is made that an arbitrary B-component always has
a boundary partner, or that the root image of Q is injective. -/
theorem finite_boundaryPartner_gives_proper_geometricSubpiece
    [Finite V]
    (A : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData A n)
    (S T : Set V) (hSclosed : A.IsClosed S)
    (hRS : Set.range d.roots ⊆ S)
    (x : {v : V // v ∉ S})
    (hxOld : x.1 ∈
      functionalComponentFrom A (Set.range d.roots) d.left)
    (hT : T = A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph S x)))
    (hTS : T ⊆ S)
    (y : {v : V // v ∉ T})
    (hSep : ¬ ReachOutside A.graph T
      (outsideCutMap hTS x) y)
    (hYBoundary : A.functionClosure
      (gaifmanNeighborhood A.graph
        (componentFrom A.graph T y)) = T)
    (a : V)
    (haOld : a ∈
      functionalComponentFrom A (Set.range d.roots) d.left)
    (haNotS : a ∉ S)
    (haNotB : a ∉ componentFrom A.graph S x) :
    ∃ (m : ℕ) (e : GeometricFunctionalPieceData A m),
      Set.range e.roots = T ∧
      componentFrom A.graph (Set.range e.roots) e.left =
        componentFrom A.graph S x ∧
      geometricPieceVertices A e ⊂ geometricPieceVertices A d := by
  have hTinside : T ⊆ geometricPieceVertices A d := by
    rw [hT]
    exact componentBoundaryClosure_inside_geometricPiece
      A d S hRS x hxOld
  obtain ⟨m, e, hRoot, _hRootS, _hLeft, _hRight, hComp⟩ :=
    finite_componentBoundary_hasGeometricPiece_of_partner
      A S T hSclosed x hT hTS y hSep hYBoundary
  have hRootInside :
      Set.range e.roots ⊆ geometricPieceVertices A d := by
    rw [hRoot]
    exact hTinside
  have hCompInside :
      componentFrom A.graph (Set.range e.roots) e.left ⊆
      componentFrom A.graph (Set.range d.roots) d.left := by
    intro z hz
    have hzB : z ∈ componentFrom A.graph S x := by
      rw [← hComp]
      exact hz
    let hCut : Set.range d.roots ⊆ S := hRS
    have hzOld :=
      componentFrom_subset_of_cut_subset A.graph hCut x hzB
    exact ⟨hzOld.1, hxOld.2.trans hzOld.2⟩
  have hPieceSubset :
      geometricPieceVertices A e ⊆ geometricPieceVertices A d := by
    intro z hz
    rcases hz with hzRoot | hzComp
    · exact hRootInside hzRoot
    · exact Or.inr (hCompInside hzComp)
  have haNotNew : a ∉ geometricPieceVertices A e := by
    intro ha
    rcases ha with haRoot | haComp
    · have haT : a ∈ T := by
        rw [← hRoot]
        exact haRoot
      exact haNotS (hTS haT)
    · have haB : a ∈ componentFrom A.graph S x := by
        rw [← hComp]
        exact haComp
      exact haNotB haB
  have hProper :
      geometricPieceVertices A e ⊂ geometricPieceVertices A d := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hPieceSubset, ?_⟩
    intro hEq
    apply haNotNew
    rw [hEq]
    exact Or.inr haOld
  exact ⟨m, e, hRoot, hComp, hProper⟩

end AllThoseRamseyClasses.Lifts
