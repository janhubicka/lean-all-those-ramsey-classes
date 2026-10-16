import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents
import AllThoseRamseyClasses.Lifts.FiniteClosedSeparatorSelection
import AllThoseRamseyClasses.Lifts.GeometricFunctionalPieces
import Mathlib.Data.Fintype.EquivFin

/-!
# Select an actual geometric forbidden piece from a weak free-amalgam obstruction

For a noninjective weak forbidden-source map into a genuine full
functional free amalgam, the preimage of the common root is closed and
separates any chosen pair of vertices mapping to opposite exclusive
sides. Finite minimal-cut selection produces an actual minimal CLOSED
separator contained in the root preimage.

Here we enumerate this entire separator by a DISTINCT ordered tuple,
producing the paper's genuine native geometric piece, with full old
relations and full function fibres. Note carefully: injectivity of
the SOURCE roots is not injectivity of their IMAGE under the weak map.
The latter is still a separate obligation for canonical lifted
relations and the full flip proof.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Reindex the same closed separating cut by an extensionally equal
root set. Both distinguished vertices are transported with their exact
complement proofs, not replaced by closure hulls. -/
theorem minimalClosedSeparator_congr_cut
    (A : Structure L V) {R S : Set V}
    (h : S = R)
    (x y : {z : V // z ∉ R})
    (hmin : IsMinimalClosedSeparator A R x y) :
    IsMinimalClosedSeparator A S
      ⟨x.1, by simpa only [h] using x.2⟩
      ⟨y.1, by simpa only [h] using y.2⟩ := by
  cases h
  exact hmin

/-- Enumerate EVERY vertex of a finite minimal closed separator
exactly once. The resulting chart is a genuine
`GeometricFunctionalPieceData`, not merely an arbitrary rooted
candidate, and retains the original two separating components. -/
theorem finiteMinimalClosedSeparator_toGeometricChart
    [Finite V]
    (A : Structure L V) (R : Set V)
    (x y : {z : V // z ∉ R})
    (hmin : IsMinimalClosedSeparator A R x y) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData A n),
      Set.range d.roots = R ∧
      d.left.1 = x.1 ∧ d.right.1 = y.1 := by
  classical
  letI : Fintype R := Fintype.ofFinite R
  let e : Fin (Fintype.card R) ≃ R := (Fintype.equivFin R).symm
  let roots : Fin (Fintype.card R) → V := fun i => (e i).1
  have hInjective : Function.Injective roots := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  have hRange : Set.range roots = R := by
    apply Set.Subset.antisymm
    · rintro z ⟨i, rfl⟩
      exact (e i).2
    · intro z hz
      obtain ⟨i, hi⟩ := e.surjective ⟨z, hz⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  let left : {z : V // z ∉ Set.range roots} :=
    ⟨x.1, by simpa only [hRange] using x.2⟩
  let right : {z : V // z ∉ Set.range roots} :=
    ⟨y.1, by simpa only [hRange] using y.2⟩
  have hMinRoots :
      IsMinimalClosedSeparator A (Set.range roots) left right := by
    exact minimalClosedSeparator_congr_cut A hRange x y hmin
  let d : GeometricFunctionalPieceData A (Fintype.card R) := {
    roots := roots
    roots_injective := hInjective
    left := left
    right := right
    minimal := hMinRoots
  }
  refine ⟨Fintype.card R, d, hRange, ?_, ?_⟩
  · rfl
  · rfl

variable {H E F W U : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L W} {Source : Structure L U}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- Given a weak map of a FINITE source, any selected left-exclusive
and right-exclusive vertices lie in opposite components of a
genuine geometric minimal-cut piece.

Its entire root vertex set is contained in the original common-root
PREIMAGE. The roots are distinct as SOURCE vertices, but their images
under the weak map are not claimed distinct. -/
theorem weakFreePartition_hasMinimalGeometricChart
    [Finite U]
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) (hf : Source.IsWeakHomomorphism Whole f)
    (x y : U)
    (hx : x ∈ weakFreeLeftPart (sL := sL) (iL := iL) f)
    (hy : y ∈ weakFreeRightPart
      (sL := sL) (iL := iL) (iR := iR) f) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData Source n),
      Set.range d.roots ⊆
        weakFreeRootPart (sL := sL) (iL := iL) f ∧
      d.left.1 = x ∧ d.right.1 = y := by
  let S : Set U := weakFreeRootPart (sL := sL) (iL := iL) f
  have hClosed : Source.IsClosed S :=
    weakFreeRootPart_isClosed (sL := sL) (iL := iL) f hf
  let xS : {z : U // z ∉ S} := ⟨x, hx.2⟩
  let yS : {z : U // z ∉ S} := ⟨y, hy.2⟩
  have hSep : ¬ ReachOutside Source.graph S xS yS :=
    weakFreePartition_root_separates_exclusive hfree f hf hx hy
  obtain ⟨R, hRS, hmin⟩ :=
    finite_exists_minimalClosedSeparator_inside
      Source S hClosed xS yS hSep
  obtain ⟨n, d, hRoot, hLeft, hRight⟩ :=
    finiteMinimalClosedSeparator_toGeometricChart Source R
      (outsideCutMap hRS xS) (outsideCutMap hRS yS) hmin
  refine ⟨n, d, ?_, ?_, ?_⟩
  · rw [hRoot]
    exact hRS
  · exact hLeft
  · exact hRight

end AllThoseRamseyClasses.Lifts
