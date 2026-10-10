import AllThoseRamseyClasses.Published.MinimalRepair4b
import PartiteConstruction.Ramsey.CopywiseRamseyTransfer

/-!
# The literal 2019 completion map preserves all irreducible B-copies

This is independent of the corrected (4b) hypothesis. The ORIGINAL
Definition 2.15 map is an induced embedding on every intrinsic
U-irreducible source restriction. If B is ordinarily irreducible,
every embedded copy of B is protected, even in a weak source.

Consequently a literal K,U-completion always supplies the
B-copywise completion required by Definition 2.17(4).

Also: the B-copywise condition pulls back through arbitrary genuine
relational embeddings of source structures. In particular it
pulls back from C induced on its whole vertex set to C itself.

Neither result assumes U-closedness of B or weakens the map notion.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {X Y Z : Type v}
variable {rules : ClosureDescription L}

/-- The 2019 map is an embedding after ANY embedding of an ordinarily
irreducible test: use its exact image as an intrinsic U-irreducible test. -/
theorem IsUHomomorphismEmbedding.after_ordinary_irreducible
    {B : RelStructure L X} {C : RelStructure L Y}
    {D : RelStructure L Z} {f : Y → Z}
    (h : IsUHomomorphismEmbedding rules C D f)
    (hB : B.Irreducible) (e : Embedding B C) :
    ∃ g : Embedding B D, ∀ x, g x = f (e x) := by
  let S : Set Y := Set.range e
  have hIrred : IsUIrreducible rules (C.induce S) :=
    (hB.range_embedding e).isUIrreducible rules
  obtain ⟨j, hj⟩ := h.embeddingOn S hIrred
  let eS : Embedding B (C.induce S) := {
    toFun := fun b => ⟨e b, ⟨b, rfl⟩⟩
    injective := by
      intro x y hxy
      exact e.injective (congrArg Subtype.val hxy)
    map_rel_iff := by
      intro R x
      change C.rel R (e ∘ x) ↔ B.rel R x
      exact e.map_rel_iff R x
  }
  exact ⟨j.comp eS, fun x => hj (eS x)⟩

/-- A literal 2019 completion in K automatically preserves all
embedded copies of any ordinarily irreducible B. -/
theorem HasLiteralUKCompletion.toCopywise
    {K : StructureClass.{u,v} (L := L)}
    {B : RelStructure L X} {C : RelStructure L Y}
    (h : HasLiteralUKCompletion K rules C)
    (hB : B.Irreducible) :
    HasCopywiseCompletion K B C := by
  obtain ⟨W, hW, Target, hK, _, f, hf⟩ := h
  exact ⟨W, hW, Target, hK, f,
    fun e => IsUHomomorphismEmbedding.after_ordinary_irreducible hf hB e⟩

/-- A B-copywise map restricts along a full source embedding.
The source can be any weak induced substructure, including an
isomorphic copy of C on the exact universe. -/
theorem CopywiseCompletion.precomp_embedding
    {B : RelStructure L X} {C : RelStructure L Y}
    {D : RelStructure L Z} {W : Type v}
    {A : RelStructure L W} {f : Y → Z}
    (h : CopywiseCompletion B C D f)
    (e : Embedding A C) :
    CopywiseCompletion B A D (f ∘ e) := by
  intro b
  obtain ⟨g, hg⟩ := h (e.comp b)
  exact ⟨g, fun x => hg x⟩

/-- A K-valued copywise completion pulls back along a genuine
source embedding, preserving the SAME target in K. -/
theorem HasCopywiseCompletion.precomp_embedding
    {K : StructureClass.{u,v} (L := L)}
    {B : RelStructure L X} {C : RelStructure L Y}
    {A : RelStructure L Z}
    (h : HasCopywiseCompletion K B C)
    (e : Embedding A C) :
    HasCopywiseCompletion K B A := by
  obtain ⟨W, hW, Target, hK, f, hf⟩ := h
  exact ⟨W, hW, Target, hK, f ∘ e,
    CopywiseCompletion.precomp_embedding hf e⟩

end AllThoseRamseyClasses.Published
