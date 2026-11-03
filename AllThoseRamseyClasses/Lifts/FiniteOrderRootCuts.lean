import PartiteConstruction.Structure.RootedOrder
import Mathlib.Data.Fintype.Card

/-!
# Track E: common-root cut ranks in finite ordered amalgamation

A finite ordered amalgam of two expanded age members must
simultaneously extend both side orders, not just the order on
their common root. For each side's root embedding f : X -> Y,
the number of embedded root vertices strictly below y in Y
provides the index of its common-root gap.

These facts are independent of any relational or functional
language. They form the numerical core of the explicit
root-cut lexicographic order on the full strong-amalgam target.
The target category and exact overlap still have to be handled
by a separate ordered amalgamation theorem.

No assumption of native expanded free amalgamation is made.
-/

namespace AllThoseRamseyClasses.Lifts

universe u v

/-- Number of vertices of a finite shared root X whose images
under f lie strictly below y. No injectivity of f is needed
for this definition or its monotonicity. -/
noncomputable def finiteRootCutRank
    {X : Type u} {Y : Type v}
    [Fintype X] [LinearOrder Y]
    (f : X → Y) (y : Y) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x : X => f x < y)).card

/-- A root-cut count is monotone as the side vertex moves
upwards in the side's linear order. -/
theorem finiteRootCutRank_mono
    {X : Type u} {Y : Type v}
    [Fintype X] [LinearOrder Y]
    (f : X → Y) :
    Monotone (finiteRootCutRank f) := by
  intro y z hyz
  unfold finiteRootCutRank
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact lt_of_lt_of_le hx hyz

/-- Whenever one selected root vertex f(x) lies before y,
the number of root vertices before y is STRICTLY larger
than the number before f(x).

This does not assume root injectivity: x itself is absent
from the first cut and present in the second. -/
theorem finiteRootCutRank_strict_after_root
    {X : Type u} {Y : Type v}
    [Fintype X] [LinearOrder Y]
    (f : X → Y) (x : X) (y : Y)
    (hxy : f x < y) :
    finiteRootCutRank f (f x) < finiteRootCutRank f y := by
  unfold finiteRootCutRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  refine ⟨x, ?_, ?_⟩
  · simp
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_filter,
      Finset.mem_univ, true_and] at hz ⊢
    rcases hz with rfl | hz
    · exact hxy
    · exact lt_trans hz hxy

/-- If the finite common root carries a linear order
and f is strictly monotone, a root vertex has exactly
its intrinsic root order rank as its cut rank.

This identity makes the root categories and side-private
categories in the eventual lexicographic amalgam key
compatible on BOTH sides. -/
theorem finiteRootCutRank_on_root
    {X : Type u} {Y : Type v}
    [Fintype X] [LinearOrder X] [LinearOrder Y]
    (f : X → Y) (hf : StrictMono f) (x : X) :
    finiteRootCutRank f (f x) =
      StructuralRamsey.Rooted.orderRank X x := by
  classical
  unfold finiteRootCutRank StructuralRamsey.Rooted.orderRank
  apply congrArg Finset.card
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hf.lt_iff_lt

end AllThoseRamseyClasses.Lifts
