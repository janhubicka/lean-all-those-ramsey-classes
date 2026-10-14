import AllThoseRamseyClasses.Applications.PosetMetricBounds
import Mathlib.Logic.Relation

/-!
# Finite-control poset transitive-closure completion

An arbitrary noninjective control map to a linear order suffices to
certify that the positive transitive closure of its source poset relation
is strict and acyclic, provided every source edge strictly increases
the control value. The reflexive-transitive closure is then a genuine
partial order, and each source edge is preserved.

This isolates the algebraic part of the corrected 2019 ordered-poset
application. It does not assert global completion on all previously
ordered pairs: that is the exact weak local quasi-cycle obstruction,
handled separately by PosetExactLocalCompletion.
-/

namespace AllThoseRamseyClasses.Applications

universe v w

/-- A source poset path strictly increases its ordered control,
even if the control map is NOT globally injective. -/
theorem poset_transGen_strict_control
    {V : Type v} {D : Type w} [Preorder D]
    (p : V → V → Prop) (f : V → D)
    (hp : ∀ x y, p x y → f x < f y)
    {x y : V} (h : Relation.TransGen p x y) :
    f x < f y := by
  induction h with
  | single hxy =>
      exact hp _ _ hxy
  | tail hxy hyz ih =>
      exact lt_trans ih (hp _ _ hyz)

/-- There are no nonempty source poset cycles. -/
theorem poset_transGen_irrefl_control
    {V : Type v} {D : Type w} [Preorder D]
    (p : V → V → Prop) (f : V → D)
    (hp : ∀ x y, p x y → f x < f y)
    (x : V) :
    ¬ Relation.TransGen p x x := by
  intro h
  exact (lt_irrefl (f x)) (poset_transGen_strict_control p f hp h)

/-- The genuine reflexive transitive closure, without any change
to the source carrier. -/
def posetReachClosure {V : Type v}
    (p : V → V → Prop) (x y : V) : Prop :=
  x = y ∨ Relation.TransGen p x y

/-- Reflexivity, transitivity, and antisymmetry of the completed poset.
No ambient linear-order extension is falsely inferred here. -/
theorem posetReachClosure_is_partial_order
    {V : Type v} {D : Type w} [Preorder D]
    (p : V → V → Prop) (f : V → D)
    (hp : ∀ x y, p x y → f x < f y) :
    (∀ x : V, posetReachClosure p x x) ∧
    (∀ x y z : V,
      posetReachClosure p x y →
      posetReachClosure p y z →
      posetReachClosure p x z) ∧
    (∀ x y : V,
      posetReachClosure p x y →
      posetReachClosure p y x → x = y) := by
  constructor
  · intro x
    exact Or.inl rfl
  constructor
  · intro x y z hxy hyz
    rcases hxy with hxy | hxy
    · subst y
      exact hyz
    rcases hyz with hyz | hyz
    · subst z
      exact Or.inr hxy
    · exact Or.inr (hxy.trans hyz)
  · intro x y hxy hyx
    rcases hxy with hxy | hxy
    · exact hxy
    rcases hyx with hyx | hyx
    · exact hyx.symm
    · exact False.elim
        ((lt_asymm (poset_transGen_strict_control p f hp hxy)
          (poset_transGen_strict_control p f hp hyx)))

/-- Every original poset edge persists in the closure. -/
theorem posetReachClosure_preserves_edges
    {V : Type v} (p : V → V → Prop)
    {x y : V} (h : p x y) :
    posetReachClosure p x y :=
  Or.inr (Relation.TransGen.single h)

/-- Every strict comparison in the completed poset strictly increases
the same original finite or infinite linear-order control. -/
theorem posetReachClosure_control_of_ne
    {V : Type v} {D : Type w} [Preorder D]
    (p : V → V → Prop) (f : V → D)
    (hp : ∀ x y, p x y → f x < f y)
    {x y : V} (h : posetReachClosure p x y)
    (hne : x ≠ y) : f x < f y := by
  rcases h with heq | hpath
  · exact (hne heq).elim
  · exact poset_transGen_strict_control p f hp hpath

end AllThoseRamseyClasses.Applications
