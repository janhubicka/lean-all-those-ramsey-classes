import PartiteConstruction.Structure.RootedOrder
import Mathlib.Data.Fintype.Card

/-!
# Track E: extend a finite ordered root across any finite full witness

The final marked-witness Ramsey transfer needs a finite witness W_B
containing an ordered expanded root B. An arbitrary full native
embedding of the old B shadow into W_B need not preserve any
pre-existing order on W_B; there is no requirement that W_B
originally carry an order.

Every injection from a linearly ordered root U into a finite
target V can be made strictly increasing by CHOOSING a linear order
on V. This construction records, for image vertices, the unique
root coordinate and uses an arbitrary finite index only as a
tie-breaker. Non-image vertices receive the bottom root coordinate.

This lemma does not use a function, relation, forbidden family,
finite expansion fibre, or Ramsey theorem. It is the precise
order-extension ingredient for selecting Bbar as the actual
canonical component lift of a native maximizing witness, with its
designated B-copy carrying the prescribed order.

No external-order compatibility is postulated or secretly inferred
from full native embeddings.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey

universe u v

/-- Every injective map of a linearly ordered type into a finite
carrier admits an order on the carrier making it strictly increasing.
The source carrier itself may be empty or infinite.

We use the lexicographic key (root position with a bottom value, arbitrary
finite target index); the second coordinate makes the key injective
even when the root position is absent. -/
theorem exists_finiteLinearOrder_extending_injection
    {U : Type u} {V : Type v}
    [LinearOrder U] [Finite V]
    (f : U → V) (hf : Function.Injective f) :
    ∃ (o : LinearOrder V),
      ∀ x y : U, x < y →
        @LT.lt V o.toLT (f x) (f y) := by
  classical
  let eV : V ≃ Fin (Nat.card V) := Finite.equivFin V
  let label : V → WithBot U :=
    fun y => if h : ∃ x : U, f x = y then
      (↑(Classical.choose h : U) : WithBot U) else ⊥
  let code : V → WithBot U ×ₗ Fin (Nat.card V) :=
    fun y => toLex (label y, eV y)
  have hcode : Function.Injective code := by
    intro x y hxy
    apply eV.injective
    exact congrArg (fun t : WithBot U ×ₗ Fin (Nat.card V) =>
      (ofLex t).2) hxy
  let o : LinearOrder V := LinearOrder.lift' code hcode
  refine ⟨o, ?_⟩
  have hlabel (x : U) : label (f x) = (x : WithBot U) := by
    change (if h : ∃ z : U, f z = f x then
      (↑(Classical.choose h : U) : WithBot U) else ⊥) = (x : WithBot U)
    have hx : ∃ z : U, f z = f x := ⟨x, rfl⟩
    rw [dif_pos hx]
    exact congrArg (fun z : U => (z : WithBot U))
      (hf (Classical.choose_spec hx))
  intro x y hxy
  change code (f x) < code (f y)
  apply Prod.Lex.toLex_lt_toLex.mpr
  left
  change label (f x) < label (f y)
  rw [hlabel x, hlabel y]
  simpa using hxy

end AllThoseRamseyClasses.Lifts
