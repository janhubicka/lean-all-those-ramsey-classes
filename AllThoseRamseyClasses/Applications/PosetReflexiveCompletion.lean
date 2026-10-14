import AllThoseRamseyClasses.Applications.PosetTransitiveClosure
import Mathlib.Order.Prod.Lex.Basic

/-!
# Ordered-poset application: reflexive input relation and order extension

Actual posets in the 2019 paper have REFLEXIVE binary order relations.
The checked strict-control transitive-closure lemma applies instead
to the kernel of NONTRIVIAL edges. We explicitly bridge these two
interfaces and construct a free linear extension by sorting vertices
by their possibly noninjective control value with a unique tie-breaker.

No monotonicity assumption on the control outside original nontrivial
relations is imposed. The resulting completion is reflexive,
transitive, antisymmetric, extends all original (also reflexive)
poset edges, and is contained in its chosen linear order.

This lemma does not assert reflection of the original absent
comparabilities on *already vertex-ordered* pairs; that is exactly
the weak-test quasi-cycle condition proved separately in PR #199.
-/

namespace AllThoseRamseyClasses.Applications

universe v w

/-- Nontrivial edges of a reflexive partial relation. -/
def posetStrictPart {V : Type v}
    (p : V → V → Prop) (x y : V) : Prop :=
  p x y ∧ x ≠ y

/-- A finite control order can be extended to a STRICT linear order
on the source, with an arbitrary tie-breaker inside each control
fibre. No injectivity of f is assumed. -/
theorem exists_linearOrder_strictOn_controlIncrease
    {V : Type v} {D : Type w} [Finite V] [LinearOrder D]
    (f : V → D) :
    ∃ (o : LinearOrder V),
      ∀ x y : V, f x < f y →
        @LT.lt V o.toLT x y := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let key : V → D ×ₗ Fin (Fintype.card V) :=
    fun x => toLex (f x, Fintype.equivFin V x)
  have hKeyInj : Function.Injective key := by
    intro x y hxy
    apply (Fintype.equivFin V).injective
    exact congrArg (fun z => (ofLex z).2) hxy
  let o : LinearOrder V := LinearOrder.lift' key hKeyInj
  refine ⟨o, ?_⟩
  intro x y hxy
  change key x < key y
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hxy)

/-- The manuscript's reflexive poset relation admits an order-
compatible partial-order completion on the SAME vertices, even
when different vertices have the same control value.

The only assumption is that each distinct positive old p-edge
strictly increases the target order. The completion does not
claim to be a full protected-map completion on originally
ordered pairs; the local obstruction lemma supplies that step. -/
theorem poset_reflexive_completion_of_strict_control
    {V : Type v} {D : Type w} [Finite V] [LinearOrder D]
    (p : V → V → Prop) (f : V → D)
    (hStrict : ∀ x y : V,
      x ≠ y → p x y → f x < f y) :
    ∃ (o : LinearOrder V) (q : V → V → Prop),
      (∀ x : V, q x x) ∧
      (∀ x y z : V, q x y → q y z → q x z) ∧
      (∀ x y : V, q x y → q y x → x = y) ∧
      (∀ x y : V, p x y → q x y) ∧
      (∀ x y : V, x ≠ y → q x y →
        @LT.lt V o.toLT x y) := by
  classical
  let ps := posetStrictPart p
  have hps : ∀ x y : V, ps x y → f x < f y := by
    intro x y hxy
    exact hStrict x y hxy.2 hxy.1
  obtain ⟨o, hOrder⟩ :=
    exists_linearOrder_strictOn_controlIncrease f
  obtain ⟨hRefl, hTrans, hAnti⟩ :=
    posetReachClosure_is_partial_order ps f hps
  refine ⟨o, posetReachClosure ps,
    hRefl, hTrans, hAnti, ?_, ?_⟩
  · intro x y hxy
    by_cases hEq : x = y
    · exact Or.inl hEq
    · exact Or.inr (Relation.TransGen.single ⟨hxy, hEq⟩)
  · intro x y hNe hReach
    exact hOrder x y
      (posetReachClosure_control_of_ne ps f hps hReach hNe)

end AllThoseRamseyClasses.Applications
