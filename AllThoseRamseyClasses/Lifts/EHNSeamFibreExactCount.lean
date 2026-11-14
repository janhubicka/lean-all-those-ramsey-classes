import AllThoseRamseyClasses.Lifts.EHNSeamFibrePairChange
import Mathlib.Tactic

/-!
# Track D: exact finite full-original-source seam fibre transfer

Counts ordered pairs of DISTINCT ORIGINAL source vertices collapsed
to a point of the actual target seam. For a one-vertex recolouring
a : s → t where s=f(a) and s ≠ t are both in the seam, the complete
new and old collision counts satisfy the subtraction-free identity

  C(new) + 2 * |f^(-1)(s) \ {a}|
      = C(old) + 2 * |f^(-1)(t)|.

In particular C(new) < C(old) iff the DESTINATION fibre is smaller
than the OLD source fibre with a removed.

These theorems are purely finite combinatorics and do NOT construct
a valid new native EHN homomorphism-embedding. Original positive
relations, set-valued function incidences (input or output), and
FULL irreducible source tests remain necessary checks.
-/

namespace AllThoseRamseyClasses.Lifts

/-- All ordered distinct original source pairs collapsed into the
ACTUAL target seam, as a finite set rather than quotient vertices. -/
noncomputable def originalSourceSeamCollisionPairs
    {V UT : Type} [Fintype V]
    (f : V → UT) (Seam : Set UT) : Finset (V × V) := by
  classical
  exact Finset.univ.filter
    (fun p => originalSourceSeamCollision f Seam p.1 p.2)

/-- OTHER original source vertices in the f-fibre of t.
Excludes a even when t=f(a); no target-root or image quotient. -/
noncomputable def originalSourceFibreExcept
    {V UT : Type} [Fintype V] [DecidableEq V]
    (f : V → UT) (a : V) (t : UT) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => u ≠ a ∧ f u = t)

/-- A one-vertex seam move creates exactly the ordered incident
pairs with original source vertices in the OLD destination fibre. -/
theorem originalSourceSeam_createdPairs_eq_incident
    {V UT : Type} [Fintype V] [DecidableEq V]
    (f : V → UT) (Seam : Set UT) (a : V) (t : UT)
    (hDifferent : f a ≠ t) (hTargetSeam : t ∈ Seam) :
    originalSourceSeamCollisionPairs
        (originalSourceSeamOneVertexRecolor f a t) Seam \
      originalSourceSeamCollisionPairs f Seam =
    originalSourceOrderedIncidentPairs a
      (originalSourceFibreExcept f a t) := by
  classical
  ext p
  simp only [Finset.mem_sdiff, originalSourceSeamCollisionPairs,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [seamFibre_oneVertex_createdCollision_iff
    f Seam a t hDifferent hTargetSeam p.1 p.2]
  constructor
  · rintro (⟨hu, hv, hft⟩ | ⟨hv, hu, hft⟩)
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      refine ⟨p.2, ?_, ?_⟩
      · simp [originalSourceFibreExcept, hv, hft]
      · apply Prod.ext
        · exact hu.symm
        · rfl
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨p.1, ?_, ?_⟩
      · simp [originalSourceFibreExcept, hu, hft]
      · apply Prod.ext
        · rfl
        · exact hv.symm
  · intro hp
    rcases Finset.mem_union.mp hp with hLeft | hRight
    · obtain ⟨u, hu, hEq⟩ := Finset.mem_image.mp hLeft
      have hFibre : u ≠ a ∧ f u = t := by
        simpa [originalSourceFibreExcept] using hu
      exact Or.inl ⟨
        (by rw [← hEq]),
        (by rw [← hEq]; exact hFibre.1),
        (by rw [← hEq]; exact hFibre.2)⟩
    · obtain ⟨u, hu, hEq⟩ := Finset.mem_image.mp hRight
      have hFibre : u ≠ a ∧ f u = t := by
        simpa [originalSourceFibreExcept] using hu
      exact Or.inr ⟨
        (by rw [← hEq]),
        (by rw [← hEq]; exact hFibre.1),
        (by rw [← hEq]; exact hFibre.2)⟩

/-- A one-vertex seam move removes exactly the ordered incident
pairs with original source vertices in the OLD source fibre. -/
theorem originalSourceSeam_removedPairs_eq_incident
    {V UT : Type} [Fintype V] [DecidableEq V]
    (f : V → UT) (Seam : Set UT) (a : V) (t : UT)
    (hDifferent : f a ≠ t) (hSourceSeam : f a ∈ Seam) :
    originalSourceSeamCollisionPairs f Seam \
      originalSourceSeamCollisionPairs
        (originalSourceSeamOneVertexRecolor f a t) Seam =
    originalSourceOrderedIncidentPairs a
      (originalSourceFibreExcept f a (f a)) := by
  classical
  ext p
  simp only [Finset.mem_sdiff, originalSourceSeamCollisionPairs,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [seamFibre_oneVertex_removedCollision_iff
    f Seam a t hDifferent hSourceSeam p.1 p.2]
  constructor
  · rintro (⟨hu, hv, hft⟩ | ⟨hv, hu, hft⟩)
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      refine ⟨p.2, ?_, ?_⟩
      · simp [originalSourceFibreExcept, hv, hft]
      · apply Prod.ext
        · exact hu.symm
        · rfl
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨p.1, ?_, ?_⟩
      · simp [originalSourceFibreExcept, hu, hft]
      · apply Prod.ext
        · rfl
        · exact hv.symm
  · intro hp
    rcases Finset.mem_union.mp hp with hLeft | hRight
    · obtain ⟨u, hu, hEq⟩ := Finset.mem_image.mp hLeft
      have hFibre : u ≠ a ∧ f u = f a := by
        simpa [originalSourceFibreExcept] using hu
      exact Or.inl ⟨
        (by rw [← hEq]),
        (by rw [← hEq]; exact hFibre.1),
        (by rw [← hEq]; exact hFibre.2)⟩
    · obtain ⟨u, hu, hEq⟩ := Finset.mem_image.mp hRight
      have hFibre : u ≠ a ∧ f u = f a := by
        simpa [originalSourceFibreExcept] using hu
      exact Or.inr ⟨
        (by rw [← hEq]),
        (by rw [← hEq]; exact hFibre.1),
        (by rw [← hEq]; exact hFibre.2)⟩

/-- Exact original-source finite seam-collision transfer balance,
without natural subtraction, assuming both actual target points
are in the seam and are distinct. -/
theorem originalSourceSeam_oneVertexRecolor_countBalance
    {V UT : Type} [Fintype V] [DecidableEq V]
    (f : V → UT) (Seam : Set UT) (a : V) (t : UT)
    (hDifferent : f a ≠ t)
    (hSourceSeam : f a ∈ Seam)
    (hTargetSeam : t ∈ Seam) :
    (originalSourceSeamCollisionPairs
        (originalSourceSeamOneVertexRecolor f a t) Seam).card +
      2 * (originalSourceFibreExcept f a (f a)).card =
    (originalSourceSeamCollisionPairs f Seam).card +
      2 * (originalSourceFibreExcept f a t).card := by
  classical
  let Old := originalSourceSeamCollisionPairs f Seam
  let New := originalSourceSeamCollisionPairs
    (originalSourceSeamOneVertexRecolor f a t) Seam
  have haS : a ∉ originalSourceFibreExcept f a (f a) := by
    simp [originalSourceFibreExcept]
  have haT : a ∉ originalSourceFibreExcept f a t := by
    simp [originalSourceFibreExcept]
  have hLost :
      (Old \ New).card =
        2 * (originalSourceFibreExcept f a (f a)).card := by
    calc
      (Old \ New).card =
          (originalSourceOrderedIncidentPairs a
            (originalSourceFibreExcept f a (f a))).card := by
            exact congrArg Finset.card
              (originalSourceSeam_removedPairs_eq_incident
                f Seam a t hDifferent hSourceSeam)
      _ = _ := originalSourceOrderedIncidentPairs_card
        a (originalSourceFibreExcept f a (f a)) haS
  have hGained :
      (New \ Old).card =
        2 * (originalSourceFibreExcept f a t).card := by
    calc
      (New \ Old).card =
          (originalSourceOrderedIncidentPairs a
            (originalSourceFibreExcept f a t)).card := by
            exact congrArg Finset.card
              (originalSourceSeam_createdPairs_eq_incident
                f Seam a t hDifferent hTargetSeam)
      _ = _ := originalSourceOrderedIncidentPairs_card
        a (originalSourceFibreExcept f a t) haT
  have hOldPartition := Finset.card_sdiff_add_card_inter Old New
  have hNewPartition := Finset.card_sdiff_add_card_inter New Old
  have hInter :
      (New ∩ Old).card = (Old ∩ New).card := by
    rw [Finset.inter_comm]
  dsimp [New, Old] at *
  omega

/-- Strictly improving one source vertex's ORIGINAL seam-collision
count is EQUIVALENT to the destination fibre being smaller than
the old source fibre AFTER removing the moved source vertex.
This is the exact k_s >= k_t + 2 criterion in natural arithmetic. -/
theorem originalSourceSeam_oneVertexRecolor_strictDrop_iff
    {V UT : Type} [Fintype V] [DecidableEq V]
    (f : V → UT) (Seam : Set UT) (a : V) (t : UT)
    (hDifferent : f a ≠ t)
    (hSourceSeam : f a ∈ Seam)
    (hTargetSeam : t ∈ Seam) :
    (originalSourceSeamCollisionPairs
        (originalSourceSeamOneVertexRecolor f a t) Seam).card <
      (originalSourceSeamCollisionPairs f Seam).card ↔
    (originalSourceFibreExcept f a t).card <
      (originalSourceFibreExcept f a (f a)).card := by
  have hBalance :=
    originalSourceSeam_oneVertexRecolor_countBalance
      f Seam a t hDifferent hSourceSeam hTargetSeam
  omega

end AllThoseRamseyClasses.Lifts
