import PartiteConstruction.Ramsey.ClosureClosedLocalFiniteness
import PartiteConstruction.Iterated.LocalTreeLike

/-!
# Definition 2.17(2): induced versus embedded closed hereditariness

The published 2019 hereditary condition quantifies over U-closed
INDUCED substructures of a member of K. The reusable Lean
\`ClosedUHereditary\` instead quantifies over arbitrary full
embeddings with possibly different vertex carriers.

These conventions agree when K is invariant under isomorphism.
A raw \`StructureClass\` is only a polymorphic predicate and does
NOT automatically carry that invariance.

We prove the missing elementary transport rather than silently
strengthening the 2019 definition. In particular, if an intrinsically
U-closed structure embeds as the induced structure on its range,
that exact induced range is intrinsically U-closed, even if the
entire target is not U-closed. No closure hull is generated.

This is unrelated to the still-open rank increment of Lemma 2.30.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {V W : Type v}

/-- Transport intrinsic U-closedness across a surjective FULL
relational embedding, i.e. an isomorphism onto the target.
No hypothesis on ambient U-closedness is used. -/
theorem isUClosed_of_surjective_embedding
    {rules : ClosureDescription L}
    {A : RelStructure L V} {B : RelStructure L W}
    (e : Embedding A B)
    (hsurj : Function.Surjective e)
    (hA : IsUClosed rules A) :
    IsUClosed rules B := by
  classical
  let h : ∀ b : W, ∃ a : V, (Embedding.id B) b = e a := by
    intro b
    obtain ⟨a, ha⟩ := hsurj b
    exact ⟨a, ha.symm⟩
  let eInv : Embedding B A :=
    (Embedding.id B).factorThroughRange e h
  have heInv (b : W) : e (eInv b) = b := by
    change e (Classical.choose (h b)) = b
    exact (Classical.choose_spec (h b)).symm
  intro rule hrule
  obtain ⟨hRoot, hUnique⟩ := hA rule hrule
  constructor
  · intro t ht
    have htA : A.rel rule.symbol (eInv ∘ t) :=
      (eInv.map_rel_iff rule.symbol t).mpr ht
    obtain ⟨rootA, hMatch⟩ := hRoot (eInv ∘ t) htA
    refine ⟨e.comp rootA, ?_⟩
    intro i
    calc
      t (i.castLE rule.rootLE) =
          e (eInv (t (i.castLE rule.rootLE))) :=
            (heInv _).symm
      _ = e (rootA i) := congrArg e (hMatch i)
  · intro rootB
    let rootA : Embedding rule.root A := eInv.comp rootB
    obtain ⟨tA, htA, hUniqueA⟩ := hUnique rootA
    let tB : Fin (L.arity rule.symbol) → W := e ∘ tA
    have htB : B.rel rule.symbol tB :=
      (e.map_rel_iff rule.symbol tA).mpr htA.1
    have hRootB (i : Fin rule.rootSize) :
        tB (i.castLE rule.rootLE) = rootB i := by
      calc
        tB (i.castLE rule.rootLE) =
            e (tA (i.castLE rule.rootLE)) := rfl
        _ = e (rootA i) := congrArg e (htA.2 i)
        _ = rootB i := heInv (rootB i)
    refine ⟨tB, ⟨htB, hRootB⟩, ?_⟩
    intro q hq
    have hqA : A.rel rule.symbol (eInv ∘ q) :=
      (eInv.map_rel_iff rule.symbol q).mpr hq.1
    have hqRootA (i : Fin rule.rootSize) :
        (eInv ∘ q) (i.castLE rule.rootLE) = rootA i :=
      congrArg eInv (hq.2 i)
    have hqEq : eInv ∘ q = tA :=
      hUniqueA (eInv ∘ q) ⟨hqA, hqRootA⟩
    funext j
    calc
      q j = e (eInv (q j)) := (heInv _).symm
      _ = e (tA j) := congrArg e (congrFun hqEq j)
      _ = tB j := rfl

/-- Every full embedding identifies its source with the exact
induced structure on its range, without closing that range in
the ambient target. -/
def inducedRangeEmbedding
    {A : RelStructure L V} {B : RelStructure L W}
    (e : Embedding A B) :
    Embedding A (B.induce (Set.range e)) where
  toFun := fun x => ⟨e x, ⟨x, rfl⟩⟩
  injective := by
    intro x y hxy
    exact e.injective (congrArg Subtype.val hxy)
  map_rel_iff := by
    intro R x
    change B.rel R (e ∘ x) ↔ A.rel R x
    exact e.map_rel_iff R x

theorem inducedRangeEmbedding_surjective
    {A : RelStructure L V} {B : RelStructure L W}
    (e : Embedding A B) :
    Function.Surjective (inducedRangeEmbedding e) := by
  rintro ⟨b, hb⟩
  obtain ⟨a, ha⟩ := hb
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact ha

/-- Intrinsic U-closedness of an embedded test transfers to
the ambient INDUCED range, without U-closedness of the ambient
target itself. -/
theorem IsUClosed.inducedRange
    {rules : ClosureDescription L}
    {A : RelStructure L V} {B : RelStructure L W}
    (hA : IsUClosed rules A) (e : Embedding A B) :
    IsUClosed rules (B.induce (Set.range e)) :=
  isUClosed_of_surjective_embedding e.inducedRangeEmbedding
    (inducedRangeEmbedding_surjective e) hA

/-- Isomorphism invariance is an explicit class property, not
part of the bare Lean type \`StructureClass\`. -/
def IsomorphismClosed2019
    (K : StructureClass.{u,v} (L := L)) : Prop :=
  ∀ {X Y : Type v}
    (A : RelStructure L X) (B : RelStructure L Y)
    (e : Embedding A B), Function.Surjective e →
      K B → K A

/-- The exact 2019 Definition 2.17(2) condition. -/
def InducedClosedHereditary2019
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L) : Prop :=
  ∀ {X : Type v} (B : RelStructure L X),
    K B → ∀ S : Set X,
      IsUClosed rules (B.induce S) → K (B.induce S)

/-- Arbitrary-embedding closed hereditariness implies the
printed 2019 induced hereditary condition, without assuming
isomorphism invariance. -/
theorem inducedClosedHereditary_of_embedded
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (h : ClosedUHereditary K rules) :
    InducedClosedHereditary2019 K rules := by
  intro X B hB S hS
  exact h (B.induce S) B hB hS (inclusion B S)

/-- Converse, with the (usually implicit) closure under
isomorphism written as an explicit hypothesis. -/
theorem embeddedClosedHereditary_of_induced
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (h : InducedClosedHereditary2019 K rules)
    (hIso : IsomorphismClosed2019 K) :
    ClosedUHereditary K rules := by
  intro X Y A B hB hClosed e
  have hRangeClosed : IsUClosed rules
      (B.induce (Set.range e)) :=
    hClosed.inducedRange e
  have hKRange : K (B.induce (Set.range e)) :=
    h B hB (Set.range e) hRangeClosed
  exact hIso A (B.induce (Set.range e))
    (inducedRangeEmbedding e)
    (inducedRangeEmbedding_surjective e) hKRange

/-- Exact equivalence of the two hereditary APIs under
isomorphism invariance; this bridges the paper to the
partite-construction library without changing its wording. -/
theorem closedHereditary2019_iff_embedded
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (hIso : IsomorphismClosed2019 K) :
    InducedClosedHereditary2019 K rules ↔
      ClosedUHereditary K rules :=
  ⟨fun h => embeddedClosedHereditary_of_induced h hIso,
   inducedClosedHereditary_of_embedded⟩

end AllThoseRamseyClasses.Published
