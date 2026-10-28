import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Why small candidate closure hulls need algebraic hypotheses

A weak source with one partial unary function may contain
a three-vertex chain x -> y -> z. Every function-closed set
containing x must then contain all three vertices. Thus the
bound |J|+1 (two vertices when |J|=1) CANNOT hold merely
from the syntax of weak partial functions.

The result is deliberately independent of metric geometry:
it does not contradict the normal-form finite-orbit theorem,
which has an additional two-step composition hypothesis.
It also does not show that such a weak candidate satisfies
the printed paper's other local-completion assumptions.
The latter source-matching obligation remains separate.

The explicit Fin 3 example is an adversarial regression against
circular attempts to first assume a bounded closed hull and
then use that hull's local completion to derive the normal
form that was needed to bound it.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Two consecutive defined values on THREE DISTINCT vertices
force every function-closed set containing the first vertex
to have at least three elements. -/
theorem threePointWeakChain_forces_closed_card_ge_three
    {A : Type u} [DecidableEq A]
    (f : A → Option A)
    (x y z : A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hfxy : f x = some y)
    (hfyz : f y = some z)
    (C : Finset A)
    (hx : x ∈ C)
    (hClosed : ∀ a b : A, a ∈ C → f a = some b → b ∈ C) :
    3 ≤ C.card := by
  have hy : y ∈ C := hClosed x y hx hfxy
  have hz : z ∈ C := hClosed y z hy hfyz
  have hsub : ({x, y, z} : Finset A) ⊆ C := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  have hcard : ({x, y, z} : Finset A).card = 3 := by
    simp [hxy, hxz, hyz]
  calc
    3 = ({x, y, z} : Finset A).card := hcard.symm
    _ ≤ C.card := Finset.card_le_card hsub

/-- A concrete weak candidate with a SINGLE partial function:
0 maps to 1, 1 maps to 2, and 2 has no image. -/
def weakThreePointChain (a : Fin 3) : Option (Fin 3) :=
  if a = 0 then some 1
  else if a = 1 then some 2
  else none

/-- The raw one-step bound |J|+1=2 fails for this single
function: every actual closed hull containing vertex 0
has cardinal at least three. This is a conditional source
obstruction, NOT a counterexample to the S-metric Ramsey theorem. -/
theorem weakThreePointChain_no_closed_hull_of_card_le_two
    (C : Finset (Fin 3))
    (h0 : (0 : Fin 3) ∈ C)
    (hClosed : ∀ a b : Fin 3, a ∈ C →
      weakThreePointChain a = some b → b ∈ C) :
    ¬ C.card ≤ 2 := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hf01 : weakThreePointChain 0 = some 1 := by decide
  have hf12 : weakThreePointChain 1 = some 2 := by decide
  have hThree : 3 ≤ C.card :=
    threePointWeakChain_forces_closed_card_ge_three
      weakThreePointChain 0 1 2 h01 h02 h12
      hf01 hf12 C h0 hClosed
  omega

end AllThoseRamseyClasses.Applications.MetricSaturation
