import AllThoseRamseyClasses.Applications.MetricRootClassCuts
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic

/-!
# Compatible order keys for rooted finite LINEARLY ORDERED class lists

The vertices of a convex S-metric amalgam must be sorted by their
jump-EQUIVALENCE CLASSES rather than the root vertices directly.
Given an ordered finite list of shared root-class labels inside each
of two ordered finite side-class lists, this file builds keys that:

* use the number of shared ROOT CLASSES strictly preceding a class;
* assign priority 2 to a shared class, independently of the side;
* assign priorities 0/1 to distinct private-side classes;
* use the original class rank to distinguish private classes in
  the same cut.

The keys are strictly increasing along either old class order
and coincide at corresponding shared classes whenever their
root class orders agree. These statements are genuinely generic
combinatorial lemmas, with no conjectural metric premises.

This is intended for the complete convex metric class amalgamation:
the actual metric class representatives and their common order are
separately established using finite jump-class-last labels and the
verified isometric root transport. The printed weak-local-completion
argument remains a distinct unverified obligation.
-/

namespace AllThoseRamseyClasses.Applications.MetricConvexOrder

universe u v w z

/-- Rank of a label in its finite ordered side-class list. -/
private noncomputable def classSideRank
    {K : Type v} [Fintype K] [LinearOrder K] (x : K) : ℕ :=
  ((Finset.univ : Finset K).filter (fun y => y < x)).card

/-- Strictly increasing rank along an actual linear side order. -/
private theorem classSideRank_strict
    {K : Type v} [Fintype K] [LinearOrder K]
    {x y : K} (hxy : x < y) :
    classSideRank x < classSideRank y := by
  classical
  unfold classSideRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  refine ⟨x, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_irrefl x
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_filter,
      Finset.mem_univ, true_and] at hz ⊢
    rcases hz with rfl | hzx
    · exact hxy
    · exact lt_trans hzx hxy

/-- A root class uses common priority 2; private-side classes use
priority 0 or 1 and their strictly increasing class rank. -/
noncomputable def classSideKey
    {R : Type u} {K : Type v}
    [Fintype R] [Fintype K] [LinearOrder K]
    (rootClass : R → K) (priority : ℕ) (x : K) :
    ℕ ×ₗ (ℕ ×ₗ ℕ) := by
  classical
  exact if hRoot : ∃ a : R, rootClass a = x then
    toLex (rootClassCut rootClass id x,
      toLex (2, rootClassCut rootClass id x))
  else
    toLex (rootClassCut rootClass id x,
      toLex (priority, classSideRank x))

/-- Shared root-class keys agree in two distinct side-class
orders when the shared root labels have identical relative
orders, even though their last members differ. -/
theorem classSideKey_root_agree
    {R : Type u} {K : Type v} {L : Type w}
    [Fintype R] [Fintype K] [Fintype L]
    [LinearOrder K] [LinearOrder L]
    (rootLeft : R → K) (rootRight : R → L)
    (hCompat : ∀ a b : R,
      rootLeft a < rootLeft b ↔ rootRight a < rootRight b)
    (a : R) :
    classSideKey rootLeft 0 (rootLeft a) =
      classSideKey rootRight 1 (rootRight a) := by
  classical
  have hL : ∃ b : R, rootLeft b = rootLeft a := ⟨a, rfl⟩
  have hR : ∃ b : R, rootRight b = rootRight a := ⟨a, rfl⟩
  simp only [classSideKey, dif_pos hL, dif_pos hR]
  rw [rootClassCut_root_agree rootLeft rootRight hCompat a]

/-- The class-side key is strictly increasing along the full
original class order. The rank distinguishes private classes,
while a shared class gets priority 2 after all private
classes in that root-class cut. -/
theorem classSideKey_strict
    {R : Type u} {K : Type v}
    [Fintype R] [Fintype K] [LinearOrder K]
    (rootClass : R → K) (priority : ℕ)
    (hPriority : priority < 2)
    {x y : K} (hxy : x < y) :
    classSideKey rootClass priority x <
      classSideKey rootClass priority y := by
  classical
  have hCut : rootClassCut rootClass id x ≤
      rootClassCut rootClass id y :=
    rootClassCut_mono rootClass id (le_of_lt hxy)
  by_cases hCutLt :
      rootClassCut rootClass id x <
        rootClassCut rootClass id y
  · unfold classSideKey
    split_ifs <;>
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hCutLt)
  · have hEq : rootClassCut rootClass id x =
        rootClassCut rootClass id y := by omega
    by_cases hRootX : ∃ a : R, rootClass a = x
    · obtain ⟨a, ha⟩ := hRootX
      have hStrict : rootClassCut rootClass id (rootClass a) <
          rootClassCut rootClass id y :=
        rootClassCut_strict_after_root rootClass id a y
          (by simpa [ha] using hxy)
      rw [ha] at hStrict
      omega
    · by_cases hRootY : ∃ a : R, rootClass a = y
      · have hLex : toLex
            (rootClassCut rootClass id x,
              toLex (priority, classSideRank x)) <
          toLex
            (rootClassCut rootClass id y,
              toLex (2, rootClassCut rootClass id y)) :=
          Prod.Lex.toLex_lt_toLex.mpr
            (Or.inr ⟨hEq,
              Prod.Lex.toLex_lt_toLex.mpr (Or.inl hPriority)⟩)
        simpa only [classSideKey, dif_neg hRootX,
          dif_pos hRootY] using hLex
      · have hRank : classSideRank x < classSideRank y :=
          classSideRank_strict hxy
        have hLex : toLex
            (rootClassCut rootClass id x,
              toLex (priority, classSideRank x)) <
          toLex
            (rootClassCut rootClass id y,
              toLex (priority, classSideRank y)) :=
          Prod.Lex.toLex_lt_toLex.mpr
            (Or.inr ⟨hEq,
              Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hRank⟩)⟩)
        simpa only [classSideKey, dif_neg hRootX,
          dif_neg hRootY] using hLex

/-- The shared/private key distinguishes two genuinely different
classes on the same side; it never collapses distinct old
j-classes before the final convex order is constructed. -/
theorem classSideKey_injective
    {R : Type u} {K : Type v}
    [Fintype R] [Fintype K] [LinearOrder K]
    (rootClass : R → K) (priority : ℕ)
    (hPriority : priority < 2) :
    Function.Injective (classSideKey rootClass priority) := by
  have hstrict : StrictMono (classSideKey rootClass priority) := by
    intro x y hxy
    exact classSideKey_strict rootClass priority hPriority hxy
  exact hstrict.injective

end AllThoseRamseyClasses.Applications.MetricConvexOrder
