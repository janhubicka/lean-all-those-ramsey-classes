import AllThoseRamseyClasses.Published.LiteralWeakRankBridge
import PartiteConstruction.Ramsey.ClosureWeakTestIntrinsicObstruction

/-!
# A cardinality obstruction for the LITERAL 2019 control map

This is an audit of original Definition 2.15, which remains
unchanged under the preferred (4b)-ONLY correction.

If a U-closed source C has a genuinely new closure output q
outside the designated root, deleting q leaves an exact
nonclosed intrinsically U-irreducible induced substructure.
Every literal 2019 U-homomorphism-embedding C -> C0 must embed
ALL of this nearly-full source test into C0.

The implication has no closed-test hypothesis and does not use
the proposed weaker IsClosedUHomomorphismEmbedding.
It is a serious size constraint on using the printed (4a)
projection during the corrected sparse Picture construction.
It does not itself refute the corrected Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U W : Type v}

/-- The exact vertex set obtained by deleting a genuine output.
The output is excluded; the original root remains. -/
def deletedOutputSet (q : U) : Set U := {x | x ≠ q}

/-- A literal U-homomorphism-embedding on a U-closed source with a
genuine closure output embeds its ENTIRE source minus that output.
This is the original Definition 2.15, not a closed-test surrogate. -/
theorem literalMap_embeds_deleted_output
    {rules : ClosureDescription L}
    {C : RelStructure L U} {Control : RelStructure L W}
    (hC : IsUClosed rules C)
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (e : Embedding rule.root C)
    (t : Fin (L.arity rule.symbol) → U)
    (ht : C.rel rule.symbol t ∧
      ∀ k : Fin rule.rootSize,
        t (k.castLE rule.rootLE) = e k)
    (j : Fin (L.arity rule.symbol))
    (hGenuine : ∀ k : Fin rule.rootSize, t j ≠ e k)
    (f : U → W)
    (hf : IsUHomomorphismEmbedding rules C Control f) :
    ∃ g : Embedding (C.induce (deletedOutputSet (t j))) Control,
      ∀ x, g x = f x.1 := by
  let S : Set U := deletedOutputSet (t j)
  have hRoot (k : Fin rule.rootSize) : e k ∈ S :=
    (hGenuine k).symm
  obtain ⟨q, hq, hUnique⟩ := (hC rule hrule).2 e
  have hT : t = q := hUnique t ht
  have hMissing :
      ∀ z : Fin (L.arity rule.symbol) → U,
        C.rel rule.symbol z →
        (∀ k : Fin rule.rootSize,
          z (k.castLE rule.rootLE) = e k) →
        ∃ k : Fin (L.arity rule.symbol), z k ∉ S := by
    intro z hz hzRoot
    have hZ : z = q := hUnique z ⟨hz, hzRoot⟩
    have hZT : z = t := hZ.trans hT.symm
    refine ⟨j, ?_⟩
    change ¬ z j ≠ t j
    exact not_not.mpr (congrFun hZT j)
  have hIrred : IsUIrreducible rules (C.induce S) :=
    IsUIrreducible.of_missing_tuple_in_weak_test
      rule hrule e S hRoot hMissing
  exact hf.embeddingOn S hIrred

/-- Finite-cardinality consequence: the literal control target has
at least as many vertices as the source with ONE output removed.
This is a necessary size inequality, not a proof of a Ramsey arrow. -/
theorem literalMap_deleted_output_card_bound
    [Finite U] [Finite W]
    {rules : ClosureDescription L}
    {C : RelStructure L U} {Control : RelStructure L W}
    (hC : IsUClosed rules C)
    (rule : ClosureRule L) (hrule : rule ∈ rules)
    (e : Embedding rule.root C)
    (t : Fin (L.arity rule.symbol) → U)
    (ht : C.rel rule.symbol t ∧
      ∀ k : Fin rule.rootSize,
        t (k.castLE rule.rootLE) = e k)
    (j : Fin (L.arity rule.symbol))
    (hGenuine : ∀ k : Fin rule.rootSize, t j ≠ e k)
    (f : U → W)
    (hf : IsUHomomorphismEmbedding rules C Control f) :
    Nat.card (deletedOutputSet (t j)) ≤ Nat.card W := by
  obtain ⟨g, _⟩ :=
    literalMap_embeds_deleted_output
      hC rule hrule e t ht j hGenuine f hf
  exact Nat.card_le_card_of_injective g g.injective

end AllThoseRamseyClasses.Published
