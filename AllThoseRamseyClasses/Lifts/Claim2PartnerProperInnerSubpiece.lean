import AllThoseRamseyClasses.Lifts.Claim2InnerBoundaryOuterLocalization
import AllThoseRamseyClasses.Lifts.ComponentBoundaryPieceCriterion

/-!
# Claim 2: genuine proper B-only inner piece from a boundary partner without intermediate left-minimality

The original outer geometric piece P = R ∪ C persists under the
contextual Claim 2 flip. Let S be ANY closed cut containing the
entire original root R. A monochromatic S-component B inside C
has full generated neighbourhood boundary T=Cl(N(B)) lying in
S ∩ P, by the independently verified source localization lemma.

Here we require the *actual* missing partner: a distinct
component after deleting T whose complete generated boundary
is also T. This is the precise converse-minimal-separator
condition; mere T ⊆ P is not enough.

The native finite boundary-partner theorem then builds a
GENUINE geometric source subpiece d with exactly root T and
selected component B. As soon as P also contains a vertex a
outside S and outside B (for example an A-exclusive vertex
while B is B-exclusive), d is a PROPER subpiece of P:
its full root and nonroot component are subsets of P,
but it omits a. The new root inherits injectivity of f
from f's InjOn T assumption.

Neither the source nor the initial/terminal EHN map is assumed
to minimize A-only support. This isolates the remaining
mathematical partner/injectivity obligations for proving that
positive local B-source rank yields a next contextual flip.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Under an actual matched second generated boundary, obtain
the genuine proper source subpiece INSIDE the current outer
geometric piece, with its whole root inside S, one-sided
nonroot component and injective ordered target-root image.

Crucially no left-support minimality assumption enters.
`AOnly` names the forbidden source vertices whose weak target
images belong to the left-exclusive region; only the
component's actual one-sidedness is used, not any new fake
quotient or source-map image closure. -/
theorem geometricPiece_properInnerOneSided_of_boundaryPartner
    [Finite V]
    (A : Structure L V)
    {n : ℕ} (P : GeometricFunctionalPieceData A n)
    (S : Set V) (hSclosed : A.IsClosed S)
    (hRS : Set.range P.roots ⊆ S)
    (x : {v : V // v ∉ S})
    (hxOld : x.1 ∈ functionalComponentFrom
      A (Set.range P.roots) P.left)
    (AOnly : Set V)
    (hBNoA : ∀ z : V,
      z ∈ componentFrom A.graph S x → z ∉ AOnly)
    (a : V)
    (haOld : a ∈ functionalComponentFrom
      A (Set.range P.roots) P.left)
    (haNotS : a ∉ S) (haAOnly : a ∈ AOnly)
    (T : Set V)
    (hT : T = A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph S x)))
    (hTS : T ⊆ S)
    (hTnonempty : T.Nonempty)
    (y : {v : V // v ∉ T})
    (hSep : ¬ ReachOutside A.graph T (outsideCutMap hTS x) y)
    (hYBoundary :
      A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph T y)) = T)
    {W : Type v} (f : V → W) (hInjT : Set.InjOn f T) :
    ∃ (m : ℕ) (d : GeometricFunctionalPieceData A m),
      0 < m ∧
      Set.range d.roots = T ∧
      Set.range d.roots ⊆ S ∩ geometricPieceVertices A P ∧
      geometricPieceVertices A d ⊂ geometricPieceVertices A P ∧
      componentFrom A.graph (Set.range d.roots) d.left =
        componentFrom A.graph S x ∧
      (∀ z : V,
        z ∈ functionalComponentFrom A
          (Set.range d.roots) d.left → z ∉ AOnly) ∧
      Function.Injective (fun i : Fin m => f (d.roots i)) := by
  classical
  obtain ⟨m, d, hDRoot, _hRootS, _hLeft, _hRight, hDComp⟩ :=
    finite_componentBoundary_hasGeometricPiece_of_partner
      A S T hSclosed x hT hTS y hSep hYBoundary
  have hCompP :
      componentFrom A.graph S x ⊆
        functionalComponentFrom A (Set.range P.roots) P.left :=
    geometricPiece_innerComponent_subset_outerComponent
      A P S hRS x hxOld
  have hBoundaryP :
      T ⊆ S ∩ geometricPieceVertices A P := by
    intro z hz
    exact geometricPiece_innerComponent_generatedBoundary_insideCut
      A P S hSclosed hRS x hxOld
      (by simpa only [hT] using hz)
  have hDRootInside :
      Set.range d.roots ⊆ S ∩ geometricPieceVertices A P := by
    intro z hz
    exact hBoundaryP (by simpa only [hDRoot] using hz)
  have hDCompInside :
      componentFrom A.graph (Set.range d.roots) d.left ⊆
        functionalComponentFrom A (Set.range P.roots) P.left := by
    intro z hz
    apply hCompP
    simpa only [hDComp] using hz
  have hPieceSubset :
      geometricPieceVertices A d ⊆
        geometricPieceVertices A P := by
    intro z hz
    rcases hz with hzRoot | hzComp
    · exact (hDRootInside hzRoot).2
    · exact Or.inr (hDCompInside hzComp)
  have haNotD : a ∉ geometricPieceVertices A d := by
    intro haD
    rcases haD with haRoot | haComp
    · exact haNotS (hDRootInside haRoot).1
    · have haB : a ∈ componentFrom A.graph S x := by
        simpa only [hDComp] using haComp
      exact hBNoA a haB haAOnly
  have hProper :
      geometricPieceVertices A d ⊂ geometricPieceVertices A P := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hPieceSubset, ?_⟩
    intro hEq
    apply haNotD
    exact hEq.symm ▸ (Or.inr haOld :
      a ∈ geometricPieceVertices A P)
  have hNoA : ∀ z : V,
      z ∈ functionalComponentFrom A
        (Set.range d.roots) d.left → z ∉ AOnly := by
    intro z hz
    apply hBNoA z
    simpa only [hDComp] using hz
  have hInj : Function.Injective
      (fun i : Fin m => f (d.roots i)) := by
    intro i j hij
    exact d.roots_injective
      (hInjT
        (by simpa only [hDRoot] using
          (show d.roots i ∈ Set.range d.roots from ⟨i, rfl⟩))
        (by simpa only [hDRoot] using
          (show d.roots j ∈ Set.range d.roots from ⟨j, rfl⟩))
        hij)
  have hm : 0 < m := by
    obtain ⟨t, ht⟩ := hTnonempty
    have htD : t ∈ Set.range d.roots := by
      simpa only [hDRoot] using ht
    obtain ⟨i, _hi⟩ := htD
    cases m with
    | zero => exact Fin.elim0 i
    | succ k => exact Nat.zero_lt_succ k
  exact ⟨m, d, hm, hDRoot, hDRootInside, hProper,
    hDComp, hNoA, hInj⟩

end AllThoseRamseyClasses.Lifts
