import AllThoseRamseyClasses.Lifts.EHNSeamFibreBalanceCounterexample
import Mathlib.Tactic

/-!
# Track D: exact original-source seam collision gain/loss witnesses

Changing one original source coordinate from s = f(a) to t in the
ACTUAL common target seam changes precisely those ordered collision
pairs which contain a. This file identifies the removed and created
pairs individually, without demanding that t is globally unused.

These are arithmetic/coordinate lemmas. They do NOT claim that the
new map satisfies EHN old relations, native functions, or FULL
irreducible source tests. The exact local EHN gate remains the
separate theorem ehn_map_changedAtOneVertex_iff_localNativeVerification.

The arbitrary-finite cardinal fibre-transfer identity and the
unrestricted original Claim 2 flip are NOT proved here.
-/

namespace AllThoseRamseyClasses.Lifts

private def oneVertexSeamRecolor
    {V UT : Type} [DecidableEq V]
    (f : V → UT) (a : V) (t : UT) : V → UT :=
  fun x => if x = a then t else f x

private def isOrderedSeamCollision
    {V UT : Type} (f : V → UT) (Seam : Set UT)
    (u v : V) : Prop :=
  u ≠ v ∧ f u = f v ∧ f u ∈ Seam

/-- A newly CREATED ordered seam-collision pair after changing
the original source vertex a from f(a) to a distinct seam point t
must be (a,u) or (u,a), with the OTHER original source vertex u
already in the full f-fibre over t. The reverse implication is
also exact, provided t belongs to the actual seam. -/
theorem seamFibre_oneVertex_createdCollision_iff
    {V UT : Type} [DecidableEq V]
    (f : V → UT) (Seam : Set UT) (a : V) (t : UT)
    (hDifferent : f a ≠ t) (hTargetSeam : t ∈ Seam)
    (u v : V) :
    (isOrderedSeamCollision (oneVertexSeamRecolor f a t) Seam u v ∧
      ¬ isOrderedSeamCollision f Seam u v) ↔
    (u = a ∧ v ≠ a ∧ f v = t) ∨
    (v = a ∧ u ≠ a ∧ f u = t) := by
  classical
  constructor
  · rintro ⟨⟨huv, hNewEq, hNewSeam⟩, hOldNot⟩
    by_cases hUa : u = a
    · have hvA : v ≠ a := by
        intro hv
        exact huv (hUa.trans hv.symm)
      have htEq : t = f v := by
        simpa [oneVertexSeamRecolor, hUa, hvA] using hNewEq
      exact Or.inl ⟨hUa, hvA, htEq.symm⟩
    · by_cases hVa : v = a
      · have hfu : f u = t := by
          simpa [oneVertexSeamRecolor, hUa, hVa] using hNewEq
        exact Or.inr ⟨hVa, hUa, hfu⟩
      · have hOldEq : f u = f v := by
          simpa [oneVertexSeamRecolor, hUa, hVa] using hNewEq
        have hOldSeam : f u ∈ Seam := by
          simpa [oneVertexSeamRecolor, hUa] using hNewSeam
        exact False.elim (hOldNot ⟨huv, hOldEq, hOldSeam⟩)
  · rintro (⟨rfl, hvA, hfv⟩ | ⟨rfl, huA, hfu⟩)
    · have hNewEq :
          oneVertexSeamRecolor f a t a =
            oneVertexSeamRecolor f a t v := by
        simp [oneVertexSeamRecolor, hvA, hfv]
      have hNewSeam :
          oneVertexSeamRecolor f a t a ∈ Seam := by
        simpa [oneVertexSeamRecolor] using hTargetSeam
      have hOldNot :
          ¬ isOrderedSeamCollision f Seam a v := by
        rintro ⟨_, hEq, _⟩
        exact hDifferent (hEq.trans hfv)
      exact ⟨⟨hvA.symm, hNewEq, hNewSeam⟩, hOldNot⟩
    · have hNewEq :
          oneVertexSeamRecolor f a t u =
            oneVertexSeamRecolor f a t a := by
        simp [oneVertexSeamRecolor, huA, hfu]
      have hNewSeam :
          oneVertexSeamRecolor f a t u ∈ Seam := by
        simpa [oneVertexSeamRecolor, huA, hfu] using hTargetSeam
      have hOldNot :
          ¬ isOrderedSeamCollision f Seam u a := by
        rintro ⟨_, hEq, _⟩
        exact hDifferent (hEq.symm.trans hfu)
      exact ⟨⟨huA, hNewEq, hNewSeam⟩, hOldNot⟩

/-- A REMOVED ordered seam-collision pair after moving a from
its old seam point f(a) to a distinct point t must have a as
exactly one endpoint, with the other endpoint belonging to
the old f-fibre over f(a). This accounts for the complete
old fibre, not merely the selected geometric root tuple. -/
theorem seamFibre_oneVertex_removedCollision_iff
    {V UT : Type} [DecidableEq V]
    (f : V → UT) (Seam : Set UT) (a : V) (t : UT)
    (hDifferent : f a ≠ t) (hSourceSeam : f a ∈ Seam)
    (u v : V) :
    (isOrderedSeamCollision f Seam u v ∧
      ¬ isOrderedSeamCollision (oneVertexSeamRecolor f a t) Seam u v) ↔
    (u = a ∧ v ≠ a ∧ f v = f a) ∨
    (v = a ∧ u ≠ a ∧ f u = f a) := by
  classical
  constructor
  · rintro ⟨⟨huv, hOldEq, hOldSeam⟩, hNewNot⟩
    by_cases hUa : u = a
    · have hvA : v ≠ a := by
        intro hv
        exact huv (hUa.trans hv.symm)
      have hfv : f v = f a := by
        simpa [hUa, eq_comm] using hOldEq
      exact Or.inl ⟨hUa, hvA, hfv⟩
    · by_cases hVa : v = a
      · have hfu : f u = f a := by
          simpa [hVa] using hOldEq
        exact Or.inr ⟨hVa, hUa, hfu⟩
      · have hNewEq :
            oneVertexSeamRecolor f a t u =
              oneVertexSeamRecolor f a t v := by
          simpa [oneVertexSeamRecolor, hUa, hVa] using hOldEq
        have hNewSeam :
            oneVertexSeamRecolor f a t u ∈ Seam := by
          simpa [oneVertexSeamRecolor, hUa] using hOldSeam
        exact False.elim (hNewNot ⟨huv, hNewEq, hNewSeam⟩)
  · rintro (⟨rfl, hvA, hfv⟩ | ⟨rfl, huA, hfu⟩)
    · have hOld : isOrderedSeamCollision f Seam a v :=
        ⟨hvA.symm, hfv.symm, hSourceSeam⟩
      have hNewNot :
          ¬ isOrderedSeamCollision
            (oneVertexSeamRecolor f a t) Seam a v := by
        rintro ⟨_, hEq, _⟩
        have htEq : t = f v := by
          simpa [oneVertexSeamRecolor, hvA] using hEq
        exact hDifferent (hfv.symm.trans htEq.symm)
      exact ⟨hOld, hNewNot⟩
    · have hOld : isOrderedSeamCollision f Seam u a := by
        refine ⟨huA, hfu, ?_⟩
        rw [hfu]
        exact hSourceSeam
      have hNewNot :
          ¬ isOrderedSeamCollision
            (oneVertexSeamRecolor f a t) Seam u a := by
        rintro ⟨_, hEq, _⟩
        have hEq' : f u = t := by
          simpa [oneVertexSeamRecolor, huA] using hEq
        exact hDifferent (hfu.symm.trans hEq')
      exact ⟨hOld, hNewNot⟩

end AllThoseRamseyClasses.Lifts
