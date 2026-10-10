import PartiteConstruction.Ramsey.ClosureDescription2019
import PartiteConstruction.Ramsey.ClosureUIrreducible2019
import PartiteConstruction.Ramsey.ClosureSemiClosed2019
import PartiteConstruction.Ramsey.AllThosePartialFiniteModels

/-!
# Published definitions, recorded without semantic strengthening

2019 Definition 2.12: closure relations have nonempty, properly shorter
irreducible roots, possibly in an infinite family of closure rules.

Definition 2.13: \`IsUClosed rules A\` means exactly one positive tuple
per embedded root; \`IsUSubstructure\` is relative to the exact induced
vertex set (Definition 2.22). \`IsUSemiClosed\` formalizes Definition 2.24.

Definition 2.15: \`IsUIrreducible\` forbids decompositions into two
proper intrinsically U-closed sides, even when the whole tested structure
is NOT U-closed. \`IsUHomomorphismEmbedding\` tests every such induced
irreducible, not merely closed ones.

These are the LITERAL definitions, kept separate from the closed-test
repair of Definition 2.17.  See docs/literal-counterexample.md.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- Ordinary irreducibility implies the literal 2019
U-irreducibility; no closure assumption is needed. -/
theorem ordinarily_irreducible_is_UIrreducible
    (rules : ClosureDescription L) (A : RelStructure L V)
    (h : A.Irreducible) : IsUIrreducible rules A :=
  h.isUIrreducible rules

/-- Full statement of published Lemma 2.23(1), reused from the
already proof-checked partite-construction repository. -/
theorem lemma_2_23_one
    (rules : ClosureDescription L) (A : RelStructure L V)
    (hA : IsUClosed rules A) (S : Set V) :
    IsUClosed rules (A.induce S) ↔ IsUSubstructure rules A S :=
  hA.induce_iff_USubstructure S

/-- Definition 2.15 grants a genuine embedding on each exact
U-irreducible induced vertex set, including nonclosed tests. -/
theorem definition_2_15_embedding_on_intrinsic_test
    {W : Type v} (rules : ClosureDescription L)
    (A : RelStructure L V) (B : RelStructure L W)
    (f : V → W) (h : IsUHomomorphismEmbedding rules A B f)
    (S : Set V) (hS : IsUIrreducible rules (A.induce S)) :
    ∃ e : Embedding (A.induce S) B, ∀ x, e x = f x.1 :=
  h.embeddingOn S hS

end AllThoseRamseyClasses.Published
