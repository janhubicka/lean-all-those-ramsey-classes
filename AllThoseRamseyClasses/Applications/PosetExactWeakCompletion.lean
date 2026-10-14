import AllThoseRamseyClasses.Applications.PosetGlobalQuasiCycle
import AllThoseRamseyClasses.Applications.PosetReflexiveCompletion

/-!
# Actual reflexive ordered-poset completion from exact weak tests

The preceding formalization established (a) a reflexive/transitive
partial-order closure under finite linear-order controls and (b)
quasi-cycle exclusion for EVERY path in the transitive closure, using
all original induced weak subsets of at most |C0| vertices.

Combine them without assuming that the original weak source is
transitive, linearly ordered, or that the control map is injective.
The resulting completion is on the SAME vertex carrier, extends
both original relations, and reflects p across all original order
comparisons. Thus the identity is protected on the two-vertex
irreducible tests most relevant for the 2019 locally finite
poset-class application.

The full `InducedClosed2019MultiamalgamationClass` still requires
transporting the precise protected relational maps, membership
test hypotheses and B-copywise conclusion; strong amalgamation
is also separate. We do not assert these class hypotheses here.
-/

namespace AllThoseRamseyClasses.Applications

universe v w

/-- Given the genuine weak exact-local hypotheses, the original
partial-order relation admits a global reflexive/transitive/
antisymmetric completion WITH FULL REFLECTION of comparisons on
old ordered pairs. This is the precise mathematical endpoint of
the finite-control quasi-cycle argument. -/
theorem poset_reflexive_completion_of_exact_weak_local_tests
    {V : Type v} {D : Type w}
    [Fintype V] [LinearOrder D] [Fintype D]
    (ord p : V → V → Prop) (f : V → D)
    (hOrd : ∀ x y : V, x ≠ y → ord x y → f x < f y)
    (hP : ∀ x y : V, p x y → ord x y)
    (hReflexive : ∀ x : V, p x x)
    (hLocal :
      ∀ S : Finset V, S.card ≤ Fintype.card D →
        ∃ q : V → V → Prop,
          (∀ a : V, q a a) ∧
          (∀ a b c : V, q a b → q b c → q a c) ∧
          (∀ x y, x ∈ S → y ∈ S → p x y → q x y) ∧
          (∀ x y, x ∈ S → y ∈ S →
            ord x y → q x y → p x y)) :
    ∃ (o : LinearOrder V) (q : V → V → Prop),
      (∀ x : V, q x x) ∧
      (∀ x y z : V, q x y → q y z → q x z) ∧
      (∀ x y : V, q x y → q y x → x = y) ∧
      (∀ x y : V, p x y → q x y) ∧
      (∀ x y : V, x ≠ y → q x y →
        @LT.lt V o.toLT x y) ∧
      (∀ x y : V, x ≠ y → ord x y →
        @LT.lt V o.toLT x y) ∧
      (∀ x y : V, ord x y → (q x y ↔ p x y)) := by
  classical
  let ps := posetStrictPart p
  have hps : ∀ x y : V, ps x y → f x < f y := by
    intro x y hxy
    exact hOrd x y hxy.2 (hP x y hxy.1)
  obtain ⟨o, hOrder⟩ :=
    exists_linearOrder_strictOn_controlIncrease f
  obtain ⟨hRefl, hTrans, hAnti⟩ :=
    posetReachClosure_is_partial_order ps f hps
  refine ⟨o, posetReachClosure ps,
    hRefl, hTrans, hAnti, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    by_cases hEq : x = y
    · exact Or.inl hEq
    · exact Or.inr (Relation.TransGen.single ⟨hxy, hEq⟩)
  · intro x y hNe hReach
    exact hOrder x y
      (posetReachClosure_control_of_ne ps f hps hReach hNe)
  · intro x y hNe hxy
    exact hOrder x y (hOrd x y hNe hxy)
  · intro x y hxy
    constructor
    · exact poset_reflexive_weak_local_reflects_reach
        ord p f hOrd hP hReflexive hLocal x y hxy
    · intro hpxy
      by_cases hEq : x = y
      · exact Or.inl hEq
      · exact Or.inr (Relation.TransGen.single ⟨hpxy, hEq⟩)

end AllThoseRamseyClasses.Applications
