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

def originalSourceSeamOneVertexRecolor
    {V UT : Type} [DecidableEq V]
    (f : V → UT) (a : V) (t : UT) : V → UT :=
  fun x => if x = a then t else f x

def originalSourceSeamCollision
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
    (originalSourceSeamCollision (originalSourceSeamOneVertexRecolor f a t) Seam u v ∧
      ¬ originalSourceSeamCollision f Seam u v) ↔
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
        simpa [originalSourceSeamOneVertexRecolor, hUa, hvA] using hNewEq
      exact Or.inl ⟨hUa, hvA, htEq.symm⟩
    · by_cases hVa : v = a
      · have hfu : f u = t := by
          simpa [originalSourceSeamOneVertexRecolor, hUa, hVa] using hNewEq
        exact Or.inr ⟨hVa, hUa, hfu⟩
      · have hOldEq : f u = f v := by
          simpa [originalSourceSeamOneVertexRecolor, hUa, hVa] using hNewEq
        have hOldSeam : f u ∈ Seam := by
          simpa [originalSourceSeamOneVertexRecolor, hUa] using hNewSeam
        exact False.elim (hOldNot ⟨huv, hOldEq, hOldSeam⟩)
  · rintro (⟨rfl, hvA, hfv⟩ | ⟨rfl, huA, hfu⟩)
    · have hNewEq :
          originalSourceSeamOneVertexRecolor f a t a =
            originalSourceSeamOneVertexRecolor f a t v := by
        simp [originalSourceSeamOneVertexRecolor, hvA, hfv]
      have hNewSeam :
          originalSourceSeamOneVertexRecolor f a t a ∈ Seam := by
        simpa [originalSourceSeamOneVertexRecolor] using hTargetSeam
      have hOldNot :
          ¬ originalSourceSeamCollision f Seam a v := by
        rintro ⟨_, hEq, _⟩
        exact hDifferent (hEq.trans hfv)
      exact ⟨⟨hvA.symm, hNewEq, hNewSeam⟩, hOldNot⟩
    · have hNewEq :
          originalSourceSeamOneVertexRecolor f a t u =
            originalSourceSeamOneVertexRecolor f a t a := by
        simp [originalSourceSeamOneVertexRecolor, huA, hfu]
      have hNewSeam :
          originalSourceSeamOneVertexRecolor f a t u ∈ Seam := by
        simpa [originalSourceSeamOneVertexRecolor, huA, hfu] using hTargetSeam
      have hOldNot :
          ¬ originalSourceSeamCollision f Seam u a := by
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
    (originalSourceSeamCollision f Seam u v ∧
      ¬ originalSourceSeamCollision (originalSourceSeamOneVertexRecolor f a t) Seam u v) ↔
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
            originalSourceSeamOneVertexRecolor f a t u =
              originalSourceSeamOneVertexRecolor f a t v := by
          simpa [originalSourceSeamOneVertexRecolor, hUa, hVa] using hOldEq
        have hNewSeam :
            originalSourceSeamOneVertexRecolor f a t u ∈ Seam := by
          simpa [originalSourceSeamOneVertexRecolor, hUa] using hOldSeam
        exact False.elim (hNewNot ⟨huv, hNewEq, hNewSeam⟩)
  · rintro (⟨rfl, hvA, hfv⟩ | ⟨rfl, huA, hfu⟩)
    · have hOld : originalSourceSeamCollision f Seam a v :=
        ⟨hvA.symm, hfv.symm, hSourceSeam⟩
      have hNewNot :
          ¬ originalSourceSeamCollision
            (originalSourceSeamOneVertexRecolor f a t) Seam a v := by
        rintro ⟨_, hEq, _⟩
        have htEq : t = f v := by
          simpa [originalSourceSeamOneVertexRecolor, hvA] using hEq
        exact hDifferent (hfv.symm.trans htEq.symm)
      exact ⟨hOld, hNewNot⟩
    · have hOld : originalSourceSeamCollision f Seam u a := by
        refine ⟨huA, hfu, ?_⟩
        rw [hfu]
        exact hSourceSeam
      have hNewNot :
          ¬ originalSourceSeamCollision
            (originalSourceSeamOneVertexRecolor f a t) Seam u a := by
        rintro ⟨_, hEq, _⟩
        have hEq' : f u = t := by
          simpa [originalSourceSeamOneVertexRecolor, huA] using hEq
        exact hDifferent (hfu.symm.trans hEq')
      exact ⟨hOld, hNewNot⟩

/-- The ordered incident pairs determined by a set of OTHER
original source vertices: both orientations of every pair (a,u).
The explicit exclusion a ∉ S makes the two images disjoint. -/
def originalSourceOrderedIncidentPairs
    {V : Type} [DecidableEq V] (a : V) (S : Finset V) :
    Finset (V × V) :=
  (S.image (fun u => (a, u))) ∪
    (S.image (fun u => (u, a)))

/-- The exact factor 2 for ordered incident original-source pairs.
This will supply the cardinal step in the full finite seam-fibre
balance formula, without treating unordered pairs as ordered. -/
theorem originalSourceOrderedIncidentPairs_card
    {V : Type} [DecidableEq V]
    (a : V) (S : Finset V) (ha : a ∉ S) :
    (originalSourceOrderedIncidentPairs a S).card = 2 * S.card := by
  classical
  have hDisjoint :
      Disjoint (S.image (fun u => (a, u)))
        (S.image (fun u => (u, a))) := by
    apply Finset.disjoint_left.mpr
    intro p hpLeft hpRight
    obtain ⟨u, hu, hpu⟩ := Finset.mem_image.mp hpLeft
    obtain ⟨v, _hv, hpv⟩ := Finset.mem_image.mp hpRight
    have hpEq : (a, u) = (v, a) := hpu.trans hpv.symm
    have hua : u = a := congrArg Prod.snd hpEq
    exact ha (hua ▸ hu)
  have hLeftInjective : Function.Injective
      (fun u : V => (a, u)) := by
    intro u v huv
    exact congrArg Prod.snd huv
  have hRightInjective : Function.Injective
      (fun u : V => (u, a)) := by
    intro u v huv
    exact congrArg Prod.fst huv
  calc
    (originalSourceOrderedIncidentPairs a S).card =
        (S.image (fun u => (a, u))).card +
          (S.image (fun u => (u, a))).card :=
      Finset.card_union_of_disjoint hDisjoint
    _ = S.card + S.card := by
      rw [Finset.card_image_of_injective S hLeftInjective,
        Finset.card_image_of_injective S hRightInjective]
    _ = 2 * S.card := by omega

end AllThoseRamseyClasses.Lifts
