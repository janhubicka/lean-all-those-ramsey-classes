import AllThoseRamseyClasses.Published.CoordinatedCycleMatching

/-!
# Actual partial-relational structures of the long-cycle gadget family

The blocks of C_k are finite matched pairs. Each of the m-1 path
gadgets uses adjacent backbone blocks plus its private D block.
The closing gadget uses the first/last backbone blocks and the
private T block. Positive binary tuples are restricted to pairs
within a single block or co-occurring in one of these triples,
and are determined there by the fixed control C0.

This is a genuine FINITE RelStructure family, NOT just a set of
vertices or an unverified mathematical picture. It is U-closed,
but it is deliberately not claimed to belong to K. In particular
its E relation need not be transitive. The full closed-test
homomorphism-embedding, (4b), exact small-test completions and
copywise contradiction are separate proof obligations.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Exactly one gadget per path edge and one closing gadget. -/
abbrev CycleGadget (k : ℕ) :=
  Fin (cycleBackboneCount k - 1) ⊕ Unit

/-- Membership of a matching block in a gadget triple.
The edge gadgets consist of b_i,b_(i+1),t_i and the closing
gadget of b_0,b_(m-1),t_*. -/
def cycleGadgetContains (k : ℕ)
    (g : CycleGadget k) (b : CycleBlock k) : Prop :=
  match g with
  | .inl i =>
      b.val = i.val ∨ b.val = i.val + 1 ∨
        b = cycleEdgePrivateBlock k i
  | .inr _ =>
      b.val = 0 ∨
      b.val = cycleBackboneCount k - 1 ∨
      b = cycleClosingPrivateBlock k

/-- Two blocks may carry joint positive tuples only when they occur
inside one of the prescribed finite gadget triples. -/
def cycleRelatedBlocks (k : ℕ) (b c : CycleBlock k) : Prop :=
  b = c ∨
    ∃ g : CycleGadget k,
      cycleGadgetContains k g b ∧ cycleGadgetContains k g c

theorem cycleRelatedBlocks_refl (k : ℕ) (b : CycleBlock k) :
    cycleRelatedBlocks k b b := Or.inl rfl

theorem cycleRelatedBlocks_symm (k : ℕ) (b c : CycleBlock k) :
    cycleRelatedBlocks k b c → cycleRelatedBlocks k c b := by
  rintro (h | ⟨g, hb, hc⟩)
  · exact Or.inl h.symm
  · exact Or.inr ⟨g, hc, hb⟩

/-- The finite gadget incidence predicate has an effective decision
procedure. This also supports explicit finite regressions. -/
instance cycleGadgetContains_decidable (k : ℕ)
    (g : CycleGadget k) (b : CycleBlock k) :
    Decidable (cycleGadgetContains k g b) := by
  cases g with
  | inl i =>
      change Decidable (b.val = i.val ∨ b.val = i.val + 1 ∨
        b = cycleEdgePrivateBlock k i)
      infer_instance
  | inr _ =>
      change Decidable (b.val = 0 ∨
        b.val = cycleBackboneCount k - 1 ∨
        b = cycleClosingPrivateBlock k)
      infer_instance

instance cycleRelatedBlocks_decidable (k : ℕ)
    (b c : CycleBlock k) :
    Decidable (cycleRelatedBlocks k b c) := by
  unfold cycleRelatedBlocks
  infer_instance

/-- The finite partial relational E-cycle source: every relation
tuple is taken from the ten-vertex control C0, but only within
one block or a single B0 gadget support. Matching M is internal
to each block and has a unique mate, independently of E. -/
abbrev cycleGadgetWitness (k : ℕ) :
    RelStructure Lang (CycleVertex k) where
  rel
    | .lt, t =>
        cycleRelatedBlocks k (t 0).1 (t 1).1 ∧
        edge CycleControlC0 .lt
          (cycleControlVertex k (t 0))
          (cycleControlVertex k (t 1))
    | .equiv, t =>
        cycleRelatedBlocks k (t 0).1 (t 1).1 ∧
        edge CycleControlC0 .equiv
          (cycleControlVertex k (t 0))
          (cycleControlVertex k (t 1))
    | .mate, t => cycleMatching k (t 0) (t 1)

/-- All three relations of the finite witness are decidable using
its concrete support and control, without classical choice. -/
instance cycleGadgetWitness_decidable (k : ℕ) (R : Symbol)
    (x y : CycleVertex k) :
    Decidable (edge (cycleGadgetWitness k) R x y) := by
  cases R <;>
    (dsimp [edge, cycleGadgetWitness, CycleControlC0, cycleMatching]
     infer_instance)

/-- Unlike K's members, the witness needs only diagonal E and a
perfect matching for its closure rule. Both hold uniformly in k. -/
theorem cycleGadgetWitness_isUClosed (k : ℕ) :
    IsUClosed mateRules (cycleGadgetWitness k) := by
  apply isUClosed_of_reflexive_E_and_total_M
  · intro x
    change ¬ (cycleRelatedBlocks k x.1 x.1 ∧
      edge CycleControlC0 .lt
        (cycleControlVertex k x) (cycleControlVertex k x))
    intro h
    have hlt : (cycleControlVertex k x).val <
        (cycleControlVertex k x).val := h.2
    omega
  · intro x
    change cycleRelatedBlocks k x.1 x.1 ∧
      edge CycleControlC0 .equiv
        (cycleControlVertex k x) (cycleControlVertex k x)
    constructor
    · exact cycleRelatedBlocks_refl k x.1
    · simp [CycleControlC0, edge]
  · intro x
    change ¬ cycleMatching k x x
    intro h
    exact h.2 rfl
  · intro x
    change ∃! y : CycleVertex k, cycleMatching k x y
    exact cycleMatching_total k x

/-- The label projection preserves positive E relation tuples.
Reflection is required only on CLOSED irreducible tests, later. -/
theorem cycleGadgetWitness_E_projects
    (k : ℕ) (x y : CycleVertex k)
    (h : edge (cycleGadgetWitness k) .equiv x y) :
    edge CycleControlC0 .equiv
      (cycleControlVertex k x) (cycleControlVertex k y) := by
  exact h.2

/-- Likewise all positive order tuples are preserved by the
gadget-control projection, but the source order is not total. -/
theorem cycleGadgetWitness_order_projects
    (k : ℕ) (x y : CycleVertex k)
    (h : edge (cycleGadgetWitness k) .lt x y) :
    edge CycleControlC0 .lt
      (cycleControlVertex k x) (cycleControlVertex k y) := by
  exact h.2

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
