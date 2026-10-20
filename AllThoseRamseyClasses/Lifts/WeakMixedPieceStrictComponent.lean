import AllThoseRamseyClasses.Lifts.GeometricFunctionalPieces
import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents
import AllThoseRamseyClasses.Lifts.SeparatorPaths
import Mathlib.Data.Set.Card

/-!
# Strict component shrinkage inside a genuine mixed geometric piece

Let R be the actual minimal function-closed separator root of a
forbidden-source geometric piece, and let S be the full preimage of
the common root of a genuine functional free amalgam. Assume R ⊆ S.

If the selected source component C of Source \ R contains a
left-exclusive distinguished vertex x and a right-exclusive vertex z,
then the x-component after deleting ALL of S is a proper subset of C.

The inclusion is pure Gaifman-path monotonicity for nested cuts.
The strictness follows from the verified fact that Gaifman components
outside S cannot contain both left- and right-exclusive vertices.
This uses neither injectivity of the weak source map nor any
artificial image quotient. Finite sources give a strict cardinal drop.

This supplies the SET-THEORETIC descent needed by the printed Claim 2.
It does not yet construct another genuine minimal closed-separator
forbidden piece of the smaller component; that remains an independent,
essential proof obligation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F W U : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L W} {Source : Structure L U}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- An actual selected minimal-cut component that meets both
exclusive sides strictly contains the component of its left root
after deleting the whole common-root preimage.

Only ordinary set inclusion is asserted; the latter smaller
component is NOT claimed to be a member of the forbidden-piece class.
The proof applies to all function arities, including nullary ones. -/
theorem weakMixedPiece_fullRootComponent_proper
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) (hf : Source.IsWeakHomomorphism Whole f)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := sL) (iL := iL) f)
    (hLeft : d.left.1 ∈
      weakFreeLeftPart (sL := sL) (iL := iL) f)
    (z : U)
    (hzComponent : z ∈ functionalComponentFrom
      Source (Set.range d.roots) d.left)
    (hzRight : z ∈ weakFreeRightPart
      (sL := sL) (iL := iL) (iR := iR) f) :
    functionalComponentFrom Source
      (weakFreeRootPart (sL := sL) (iL := iL) f)
      ⟨d.left.1, hLeft.2⟩ ⊂
    functionalComponentFrom Source (Set.range d.roots) d.left := by
  let S : Set U := weakFreeRootPart (sL := sL) (iL := iL) f
  let R : Set U := Set.range d.roots
  let xS : {v : U // v ∉ S} := ⟨d.left.1, hLeft.2⟩
  have hCutRoot : outsideCutMap hRoots xS = d.left := by
    apply Subtype.ext
    rfl
  have hSubset :
      functionalComponentFrom Source S xS ⊆
        functionalComponentFrom Source R d.left := by
    have hMono :=
      componentFrom_subset_of_cut_subset Source.graph hRoots xS
    simpa only [functionalComponentFrom, hCutRoot] using hMono
  have hzNotSmall :
      z ∉ functionalComponentFrom Source S xS := by
    intro hzSmall
    have hzLeft :
        z ∈ weakFreeLeftPart (sL := sL) (iL := iL) f :=
      weakFreePartition_component_left hfree f hf xS hLeft hzSmall
    exact (Set.disjoint_left.mp
      (weakFreePartition_left_right_disjoint hfree f)) hzLeft hzRight
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨hSubset, ?_⟩
  intro hEq
  apply hzNotSmall
  rw [hEq]
  exact hzComponent

/-- In a finite original forbidden source, removing the full
common-root preimage gives strictly fewer vertices in the selected
left Gaifman component than removing only its minimal separating
root R. No claim of a smaller *forbidden* piece is made. -/
theorem weakMixedPiece_fullRootComponent_strictCount
    [Finite U]
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) (hf : Source.IsWeakHomomorphism Whole f)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := sL) (iL := iL) f)
    (hLeft : d.left.1 ∈
      weakFreeLeftPart (sL := sL) (iL := iL) f)
    (z : U)
    (hzComponent : z ∈ functionalComponentFrom
      Source (Set.range d.roots) d.left)
    (hzRight : z ∈ weakFreeRightPart
      (sL := sL) (iL := iL) (iR := iR) f) :
    (functionalComponentFrom Source
      (weakFreeRootPart (sL := sL) (iL := iL) f)
      ⟨d.left.1, hLeft.2⟩).ncard <
    (functionalComponentFrom Source
      (Set.range d.roots) d.left).ncard := by
  exact Set.ncard_lt_ncard
    (weakMixedPiece_fullRootComponent_proper
      hfree f hf d hRoots hLeft z hzComponent hzRight)

end AllThoseRamseyClasses.Lifts
