import AllThoseRamseyClasses.Lifts.Claim2InnerBoundaryOuterLocalization
import AllThoseRamseyClasses.Lifts.ExactOppositeBoundarySeparator
import AllThoseRamseyClasses.Lifts.WeakMinimalGeometricChart
import AllThoseRamseyClasses.Lifts.PositiveGeometricRootFromConnectedPath

/-!
# Track C: exact partner-or-smaller-root dichotomy inside any geometric outer piece

Suppose an intermediate native source (NOT assumed A-support-minimal)
has an actual outer geometric piece P = R ∪ C, a closed cut S
containing R, and a selected component B of Source minus S
inside C. Let T = Cl_Source(N_Source(B)) be its complete
function-generated boundary.

The checked source localization lemma guarantees T ⊆ S ∩ P.
After deleting T the entire B-component is EXACTLY unchanged.

Choose an opposite vertex y in a different T-component.
Let U = Cl_Source(N_Source(C_T(y))). This U is an actual closed
subset of T. There is an exhaustive source-geometric dichotomy:

* U=T: y is a genuine full generated-boundary PARTNER for B,
  so the existing partner-based proper B-only flip applies
  once root image injectivity is separately supplied.
* U ⊂ T: U itself is a GENUINE minimal closed separator of
  the two selected original source vertices, and on a finite
  carrier is the FULL root of an actual geometric piece whose
  root lies STRICTLY inside T and hence inside S∩P.

This removes any need to posit an additional minimal separator
in the uncovered-boundary case, using exact native functional
closure rather than a Gaifman-graph-only cut. No weak-map
injection or intermediate A-minimality is used.

Importantly the new smaller-root piece is not claimed one-sided:
its chosen component may enlarge when the cut shrinks. Therefore
the dichotomy does NOT by itself produce an unrestricted
positive-B-rank successor or complete Claim 2.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A true S-component inside an outer geometric piece either
has a full boundary partner after its exact T cut or else the
opposite side generates a STRICTLY smaller genuine source
minimal-separator root U inside S∩P.

The root of the newly selected piece is exactly U, not a
conjectural or arbitrarily chosen smaller completion. -/
theorem geometricInnerBoundary_partner_or_smallerRoot
    [Finite V]
    (A : Structure L V)
    {n : ℕ} (P : GeometricFunctionalPieceData A n)
    (S : Set V) (hSclosed : A.IsClosed S)
    (hOuterRootInS : Set.range P.roots ⊆ S)
    (x : {v : V // v ∉ S})
    (hxOuter : x.1 ∈ functionalComponentFrom A
      (Set.range P.roots) P.left)
    (T : Set V)
    (hT : T = A.functionClosure
      (gaifmanNeighborhood A.graph
        (componentFrom A.graph S x)))
    (hTS : T ⊆ S)
    (y : {v : V // v ∉ T})
    (hSeparated : ¬ ReachOutside A.graph T
      (outsideCutMap hTS x) y) :
    (A.functionClosure
       (gaifmanNeighborhood A.graph
         (componentFrom A.graph T y)) = T) ∨
    (∃ (m : ℕ) (d : GeometricFunctionalPieceData A m),
      Set.range d.roots ⊂ T ∧
      Set.range d.roots ⊆ S ∩ geometricPieceVertices A P ∧
      d.left.1 = x.1 ∧ d.right.1 = y.1 ∧
      Set.range d.roots =
        A.functionClosure
          (gaifmanNeighborhood A.graph
            (componentFrom A.graph T y))) := by
  classical
  let U : Set V :=
    A.functionClosure
      (gaifmanNeighborhood A.graph
        (componentFrom A.graph T y))
  let xT : {v : V // v ∉ T} := outsideCutMap hTS x
  have hTclosed : A.IsClosed T := by
    rw [hT]
    exact A.functionClosure_isClosed _
  have hCsame :
      componentFrom A.graph T xT =
        componentFrom A.graph S x := by
    cases hT
    exact componentBoundaryClosure_preserves_exact_component
      A S hSclosed x
  have hFullX :
      A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph T xT)) = T := by
    rw [hCsame]
    exact hT.symm
  have hUT : U ⊆ T :=
    functionalClosure_neighborhood_subset_cut A T hTclosed y
  by_cases hPartner : U = T
  · exact Or.inl hPartner
  · right
    have hProper : U ⊂ T :=
      Set.ssubset_iff_subset_ne.mpr ⟨hUT, hPartner⟩
    have hMin : IsMinimalClosedSeparator A U
        (outsideCutMap hUT xT) (outsideCutMap hUT y) :=
      oppositeBoundaryClosure_isMinimalClosedSeparator
        A T hTclosed xT y hSeparated hFullX
    obtain ⟨m, d, hRoot, hLeft, hRight⟩ :=
      finiteMinimalClosedSeparator_toGeometricChart
        A U (outsideCutMap hUT xT) (outsideCutMap hUT y) hMin
    have hTInside :
        T ⊆ S ∩ geometricPieceVertices A P := by
      intro z hz
      exact geometricPiece_innerComponent_generatedBoundary_insideCut
        A P S hSclosed hOuterRootInS x hxOuter
        (by simpa only [hT] using hz)
    have hRootInside :
        Set.range d.roots ⊆
          S ∩ geometricPieceVertices A P := by
      intro z hz
      exact hTInside (hUT (by simpa only [hRoot] using hz))
    exact ⟨m, d, by simpa only [hRoot] using hProper,
      hRootInside, hLeft, hRight, hRoot⟩

/-- In a source whose two selected opposing vertices are joined
by a genuine Gaifman path, the strictly smaller root of the
uncovered-boundary alternative is automatically NONEMPTY.

This guarantees positive root arity for the original-2019
global canonical piece relation in the root-shrinking case.
No intermediate A-support minimality or global weak-image
injectivity is introduced. -/
theorem geometricInnerBoundary_partner_or_positiveSmallerRoot
    [Finite V]
    (A : Structure L V)
    {n : ℕ} (P : GeometricFunctionalPieceData A n)
    (S : Set V) (hSclosed : A.IsClosed S)
    (hOuterRootInS : Set.range P.roots ⊆ S)
    (x : {v : V // v ∉ S})
    (hxOuter : x.1 ∈ functionalComponentFrom A
      (Set.range P.roots) P.left)
    (T : Set V)
    (hT : T = A.functionClosure
      (gaifmanNeighborhood A.graph
        (componentFrom A.graph S x)))
    (hTS : T ⊆ S)
    (y : {v : V // v ∉ T})
    (hSeparated : ¬ ReachOutside A.graph T
      (outsideCutMap hTS x) y)
    (hConnected : ReachOutside A.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {v : V // v ∉ ∅})
      (⟨y.1, by simp⟩ : {v : V // v ∉ ∅})) :
    (A.functionClosure
       (gaifmanNeighborhood A.graph
         (componentFrom A.graph T y)) = T) ∨
    (∃ (m : ℕ) (d : GeometricFunctionalPieceData A m),
      0 < m ∧
      Set.range d.roots ⊂ T ∧
      Set.range d.roots ⊆ S ∩ geometricPieceVertices A P ∧
      d.left.1 = x.1 ∧ d.right.1 = y.1 ∧
      Set.range d.roots =
        A.functionClosure
          (gaifmanNeighborhood A.graph
            (componentFrom A.graph T y))) := by
  rcases geometricInnerBoundary_partner_or_smallerRoot
      A P S hSclosed hOuterRootInS x hxOuter
      T hT hTS y hSeparated with
    hPartner | ⟨m, d, hProper, hRootInside, hLeft, hRight, hRoot⟩
  · exact Or.inl hPartner
  · right
    have hConnectedD : ReachOutside A.graph (∅ : Set V)
        (⟨d.left.1, by simp⟩ : {v : V // v ∉ ∅})
        (⟨d.right.1, by simp⟩ : {v : V // v ∉ ∅}) := by
      simpa only [hLeft, hRight] using hConnected
    have hNonempty : (Set.range d.roots).Nonempty :=
      minimalClosedSeparator_nonempty_of_emptyCut_path
        A (Set.range d.roots) d.left d.right d.minimal
        hConnectedD
    obtain ⟨z, hz⟩ := hNonempty
    obtain ⟨i, _hi⟩ := hz
    have hm : 0 < m := by
      cases m with
      | zero => exact Fin.elim0 i
      | succ k => exact Nat.zero_lt_succ k
    exact ⟨m, d, hm, hProper, hRootInside,
      hLeft, hRight, hRoot⟩


end AllThoseRamseyClasses.Lifts
