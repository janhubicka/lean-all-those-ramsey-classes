import AllThoseRamseyClasses.Lifts.WeakSourceComponentIndices
import Mathlib.Data.Set.Card

/-!
# Strict component-count decrease when restricting to a selected mixed piece

The multicomponent obstruction in Section 3 is now expressed by
genuine source Gaifman component indices of the graph outside the
preimage S=f^{-1}(X) of the common functional root.

An actual minimal separator R ⊆ S of x (left-exclusive) and
y (right-exclusive), with chosen x-component C of Source\R, cannot
contain ANY right-exclusive vertex belonging to the same
Source\S component as y. Thus the set of right-exclusive
component indices met by C is a PROPER SUBSET of all
right-exclusive component indices in the full source.

For a finite source this gives a STRICT natural-number decrease.
It is a true finite combinatorial parameter for future Claim 2
induction, but is NOT YET a decrease between forbidden witnesses
under a flip. No homomorphism-embedding injectivity is used.
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

/-- Exactly those right-exclusive SOURCE-minus-common-root
component classes containing a vertex in the selected native
minimal-cut left component. The full separator root R itself
cannot contribute any right-exclusive vertex when R⊆S. -/
def weakRightComponentIdsInPiece
    (f : U → W)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n) :
    Set (FunctionalOutsideComponentId Source
      (weakFreeRootPart (sL := sL) (iL := iL) f)) :=
  {c | ∃ (z : U) (hz : z ∈
      weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f),
    z ∈ functionalComponentFrom Source (Set.range d.roots) d.left ∧
    functionalOutsideComponentId Source
      (weakFreeRootPart (sL := sL) (iL := iL) f)
      ⟨z, hz.2⟩ = c}

/-- Every right-exclusive component class occurring in the
selected geometric piece already occurs in the full source. -/
theorem weakRightComponentIdsInPiece_subset_all
    (f : U → W)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n) :
    weakRightComponentIdsInPiece
      (Source := Source) (sL := sL) (iL := iL)
      (iR := iR) f d ⊆
    weakRightExclusiveComponentIds
      (Source := Source) (sL := sL) (iL := iL)
      (iR := iR) f := by
  rintro c ⟨z, hz, _hzComponent, hzId⟩
  exact ⟨z, hz, hzId⟩

/-- The designated right-exclusive component used for the cut
selection is NEVER met by the selected left component. This
excludes an entire Gaifman component, not merely one vertex. -/
theorem weakRightComponentId_chosenRight_not_inPiece
    (f : U → W)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := sL) (iL := iL) f)
    (y : U)
    (hy : y ∈ weakFreeRightPart
      (sL := sL) (iL := iL) (iR := iR) f)
    (hRight : d.right.1 = y) :
    functionalOutsideComponentId Source
      (weakFreeRootPart (sL := sL) (iL := iL) f)
      ⟨y, hy.2⟩ ∉
    weakRightComponentIdsInPiece
      (Source := Source) (sL := sL) (iL := iL)
      (iR := iR) f d := by
  rintro ⟨z, hzRight, hzComponent, hzId⟩
  exact (weakMixedPiece_rightComponentId_ne
    f d hRoots y hy hRight z hzComponent hzRight) hzId.symm

/-- The selected piece meets strictly FEWER distinct
right-exclusive source components than the full source,
provided the genuine minimal cut roots lie in the common
root preimage and its designated right root is right-exclusive.

This comparison involves a piece of the SAME original
forbidden source; it does not assert a replacement source
or a completed Claim 2 flip. -/
theorem weakRightComponentIdsInPiece_strict_count
    [Finite U]
    (f : U → W)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := sL) (iL := iL) f)
    (y : U)
    (hy : y ∈ weakFreeRightPart
      (sL := sL) (iL := iL) (iR := iR) f)
    (hRight : d.right.1 = y) :
    (weakRightComponentIdsInPiece
      (Source := Source) (sL := sL) (iL := iL)
      (iR := iR) f d).ncard <
    (weakRightExclusiveComponentIds
      (Source := Source) (sL := sL) (iL := iL)
      (iR := iR) f).ncard := by
  classical
  let S : Set U :=
    weakFreeRootPart (sL := sL) (iL := iL) f
  letI : Finite (FunctionalOutsideComponentId Source S) :=
    finite_functionalOutsideComponentId Source S
  let C :=
    weakRightComponentIdsInPiece
      (Source := Source) (sL := sL) (iL := iL)
      (iR := iR) f d
  let D :=
    weakRightExclusiveComponentIds
      (Source := Source) (sL := sL) (iL := iL)
      (iR := iR) f
  have hCD : C ⊆ D :=
    weakRightComponentIdsInPiece_subset_all f d
  have hYinD :
      functionalOutsideComponentId Source S
        ⟨y, hy.2⟩ ∈ D := by
    exact ⟨y, hy, rfl⟩
  have hYnotC :
      functionalOutsideComponentId Source S
        ⟨y, hy.2⟩ ∉ C :=
    weakRightComponentId_chosenRight_not_inPiece
      f d hRoots y hy hRight
  have hCDne : C ≠ D := by
    intro h
    apply hYnotC
    rw [h]
    exact hYinD
  have hProper : C ⊂ D :=
    Set.ssubset_iff_subset_ne.mpr ⟨hCD, hCDne⟩
  exact Set.ncard_lt_ncard hProper

end AllThoseRamseyClasses.Lifts
