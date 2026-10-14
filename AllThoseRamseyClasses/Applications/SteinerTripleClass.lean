import AllThoseRamseyClasses.Published.InducedClosed2019ClassBridge
import Mathlib.Tactic

/-!
# Free-order partial Steiner triples: faithful relational language

A marked ordered pair is in `covered` exactly when it belongs to a
block. The ternary `block x y z` names the unique completion of the
increasing covered pair `x<y`. An uncovered pair is deliberately NOT a
root of a closure rule. This is necessary for partial Steiner systems.

The class below includes an explicit exact-root witness in its initial
normal-form axioms. This keeps the first closure verification independent
of a later, separately audited equivalence with the conventional
unordered 3-set presentation. It is NOT yet a proof of the class's
strong amalgamation or local-completion conditions.
-/

namespace AllThoseRamseyClasses.Applications.SteinerTriples

open StructuralRamsey
open StructuralRamsey.RelStructure

inductive Symbol
  | order | covered | block
  deriving DecidableEq

abbrev Lang : RelLanguage where
  Symbol := Symbol
  arity
    | .order => 2
    | .covered => 2
    | .block => 3

def edge {V : Type} (C : RelStructure Lang V) (R : Symbol)
    (x y : V) : Prop :=
  C.rel R ![x, y]

def triple {V : Type} (C : RelStructure Lang V)
    (x y z : V) : Prop :=
  C.rel .block ![x, y, z]

/-- The unique root type: an increasing, marked pair, and no block
on its two vertices. A pair that is not marked is not a root. -/
abbrev pairRoot : RelStructure Lang (Fin 2) where
  rel
    | .order, t => t 0 = 0 ∧ t 1 = 1
    | .covered, t => t 0 = 0 ∧ t 1 = 1
    | .block, _ => False

private theorem pairRoot_irreducible : pairRoot.Irreducible := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · exact False.elim (hab rfl)
  · exact ⟨.order, ![(0 : Fin 2), 1], 0, 1, by decide, rfl, rfl⟩
  · exact ⟨.order, ![(0 : Fin 2), 1], 1, 0, by decide, rfl, rfl⟩
  · exact False.elim (hab rfl)

/-- The 2019-style relational rule: exactly one third vertex above
each increasing covered pair, not above every pair. -/
abbrev blockRule : ClosureRule Lang where
  symbol := .block
  rootSize := 2
  rootPositive := by decide
  rootStrict := by decide
  root := pairRoot
  rootIrreducible := pairRoot_irreducible

abbrev blockRules : ClosureDescription Lang := {blockRule}

/-- Normal-form laws for a finite linearly ordered partial Steiner
triple system. `covered_root` states the exact induced two-vertex
root condition; a later bridge to unordered blocks should derive it
rather than assume it for arbitrary hypergraphs. -/
structure IsOrderedPartialSteinerTriple {V : Type}
    (C : RelStructure Lang V) : Prop where
  finite : Finite V
  order_irrefl : ∀ x : V, ¬ edge C .order x x
  order_trans : ∀ x y z : V,
    edge C .order x y → edge C .order y z → edge C .order x z
  order_total : ∀ x y : V, x ≠ y →
    edge C .order x y ∨ edge C .order y x
  covered_implies_order : ∀ x y : V,
    edge C .covered x y → edge C .order x y
  covered_root : ∀ x y : V, edge C .covered x y →
    ∃ e : Embedding pairRoot C, e 0 = x ∧ e 1 = y
  block_valid : ∀ x y z : V,
    triple C x y z → edge C .covered x y
  block_distinct : ∀ x y z : V, triple C x y z →
    x ≠ y ∧ x ≠ z ∧ y ≠ z
  covered_has_block : ∀ x y : V,
    edge C .covered x y → ∃ z : V, triple C x y z
  block_unique : ∀ x y z w : V,
    triple C x y z → triple C x y w → z = w
  other_pairs : ∀ x y z : V, triple C x y z →
    ((triple C x z y ∧ edge C .order x z) ∨
      (triple C z x y ∧ edge C .order z x)) ∧
    ((triple C y z x ∧ edge C .order y z) ∨
      (triple C z y x ∧ edge C .order z y))

def orderedSteinerClass : StructureClass (L := Lang) :=
  fun {V} (C : RelStructure Lang V) => IsOrderedPartialSteinerTriple C

/-- The arbitrary order alone witnesses ordinary irreducibility,
independently of any closure assumptions. -/
theorem orderedSteiner_irreducible {V : Type}
    (C : RelStructure Lang V) (hC : IsOrderedPartialSteinerTriple C) :
    C.Irreducible := by
  intro x y hxy
  rcases hC.order_total x y hxy with h | h
  · exact ⟨.order, ![x, y], 0, 1, h, rfl, rfl⟩
  · exact ⟨.order, ![y, x], 1, 0, h, rfl, rfl⟩

/-- Every well-formed ordered partial Steiner triple system is closed
under exactly the designated marked-pair rule. The argument includes
both (i) validity of the full induced root of EVERY block tuple and
(ii) unique block completion of every embedded root. -/
theorem orderedSteiner_isUClosed {V : Type}
    (C : RelStructure Lang V) (hC : IsOrderedPartialSteinerTriple C) :
    IsUClosed blockRules C := by
  intro rule hrule
  have heq : rule = blockRule := by
    simpa only [blockRules, Set.mem_singleton_iff] using hrule
  subst rule
  constructor
  · intro t ht
    obtain ⟨e, he0, he1⟩ :=
      hC.covered_root (t 0) (t 1) (hC.block_valid _ _ _ ht)
    refine ⟨e, ?_⟩
    intro i
    fin_cases i
    · exact he0.symm
    · exact he1.symm
  · intro e
    have hRootCovered : edge pairRoot .covered 0 1 := by decide
    have hCovered : edge C .covered (e 0) (e 1) := by
      change C.rel .covered (e ∘ ![(0 : Fin 2), 1])
      exact (e.map_rel_iff .covered ![(0 : Fin 2), 1]).mpr hRootCovered
    obtain ⟨z, hz⟩ := hC.covered_has_block (e 0) (e 1) hCovered
    refine ⟨![e 0, e 1, z], ⟨hz, ?_⟩, ?_⟩
    · intro i
      fin_cases i <;> rfl
    · intro t ht
      have ht0 : t 0 = e 0 := ht.2 0
      have ht1 : t 1 = e 1 := ht.2 1
      have hz' : triple C (e 0) (e 1) (t 2) := by
        change C.rel .block ![e 0, e 1, t 2]
        have htuple : (![e 0, e 1, t 2] : Fin 3 → V) = t := by
          funext i
          fin_cases i <;> simp [ht0, ht1]
        rw [htuple]
        exact ht.1
      have hlast : t 2 = z :=
        hC.block_unique _ _ _ _ hz' hz
      funext i
      fin_cases i
      · exact ht0
      · exact ht1
      · exact hlast

end AllThoseRamseyClasses.Applications.SteinerTriples
