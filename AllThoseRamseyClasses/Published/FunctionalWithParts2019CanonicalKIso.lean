import AllThoseRamseyClasses.Published.FunctionalWithParts2019CanonicalKClass
import AllThoseRamseyClasses.Published.InducedClosed2019HereditaryBridge
import PartiteConstruction.Functional.WholeMaskPartiteRamseyArrow2019
import PartiteConstruction.Functional.WholeMaskTagArrow2019

/-!
# The genuine canonical partite functional K image respects isomorphisms

An abstract 2019 relational StructureClass need not be isomorphism
invariant.  For the canonical tagged class constructed from a genuine
part-labelled partial-function class H, the missing invariance follows
provided H itself is invariant under full PART-PRESERVING bijective
functional embeddings.

Given a relational isomorphism of a source E onto a canonical tagged
H-target, pull the genuine Option(Set) functions and vertex part map
back along its vertex bijection. The verified full canonical tagged
embedding functor shows E is LITERALLY the canonical presentation of
that pulled-back structure on the ORIGINAL vertex set. No new points,
closure hulls or changed partial definedness are introduced.

This proves the exact class-isomorphism hypothesis needed for the
corrected 2019 Theorem 2.18; it does not infer the original H-class's
isomorphism invariance, which must be a normal class assumption.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {X Y : Type w}

/-- Pullback of genuine partial functions along a vertex bijection.
Defined-empty and undefined are unchanged under Option.map. -/
private noncomputable def partialPullback
    (B : PartialSetStructure L Y) (e : X ≃ Y) :
    PartialSetStructure L X where
  rel R xs := B.rel R (e ∘ xs)
  func F xs := (B.func F (e ∘ xs)).map
    (fun U => e.symm '' U)

/-- A vertex bijection is a FULL genuine partial-function embedding
of the pulled-back structure. This reflects even missing domains. -/
private def pullbackFullEmbedding
    (B : PartialSetStructure L Y) (e : X ≃ Y) :
    PartialSetStructure.Embedding (partialPullback B e) B where
  toFun := e
  injective := e.injective
  map_rel_iff := fun _ _ => Iff.rfl
  map_func := by
    intro F xs
    change
      ((B.func F (e ∘ xs)).map
        (fun U => e.symm '' U)).map
        (Structure.imageSet e) = B.func F (e ∘ xs)
    cases hB : B.func F (e ∘ xs) with
    | none => rfl
    | some T =>
        simp only [Option.map_some]
        congr 1
        ext y
        constructor
        · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
          simpa using hz
        · intro hy
          exact ⟨e.symm y, ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩

/-- Transversal output fibres pull back through a bijection.
Each output set is carried ONTO the original complete target set. -/
private theorem pullbackTransversal
    (B : PartialSetStructure L Y) (partB : Y → Parts)
    (hTr : FibreTransversal B partB) (e : X ≃ Y) :
    FibreTransversal (partialPullback B e) (partB ∘ e) := by
  intro F xs U hVal y hy z hz hPart
  let emb := pullbackFullEmbedding B e
  have he : B.func F (e ∘ xs) =
      some (Structure.imageSet e U) := by
    have hm := emb.map_func F xs
    rw [hVal] at hm
    exact hm.symm
  have hyB : e y ∈ Structure.imageSet e U := ⟨y, hy, rfl⟩
  have hzB : e z ∈ Structure.imageSet e U := ⟨z, hz, rfl⟩
  exact e.injective
    (hTr F (e ∘ xs) (Structure.imageSet e U) he
      (e y) hyB (e z) hzB hPart)

/-- Isomorphism invariance of the actual genuine functional
PARTITE class, stated on whole-value full functional embeddings. -/
def GenuinePartiteIsomorphismClosed2019
    (H : GenuinePartite2019Class (L := L) (Parts := Parts)) : Prop :=
  ∀ {U V : Type w} [Finite U] [Finite V]
    (A : PartialSetStructure L U) (partA : U → Parts)
    (B : PartialSetStructure L V) (partB : V → Parts),
    H B partB →
    ∀ (f : PartPreservingEmbedding A partA B partB),
      Function.Surjective f.1.toFun → H A partA

/-- The canonical tagged image of an isomorphism-closed genuine
partite functional class is an isomorphism-closed relational class.
The pulled-back source structure is canonical on its SAME carrier. -/
theorem canonicalGenuineTagged2019Class_isomorphismClosed
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hIso : GenuinePartiteIsomorphismClosed2019 H) :
    IsomorphismClosed2019 (canonicalGenuineTagged2019Class H) := by
  classical
  intro U V Source Tagged j hSurj hK
  obtain ⟨hFinite, B, partB, hHB, hTrB, hEq⟩ := hK
  letI : Finite V := hFinite
  letI : Finite U := Finite.of_injective j.toFun j.injective
  cases hEq
  let e : U ≃ V := Equiv.ofBijective j.toFun ⟨j.injective, hSurj⟩
  let A : PartialSetStructure L U := partialPullback B e
  let partA : U → Parts := partB ∘ e
  let emb : PartialSetStructure.Embedding A B :=
    pullbackFullEmbedding B e
  let embPart : PartPreservingEmbedding A partA B partB :=
    ⟨emb, fun _ => rfl⟩
  have hA : H A partA := hIso A partA B partB hHB embPart hSurj
  have hTransA : FibreTransversal A partA :=
    pullbackTransversal B partB hTrB e
  let embTag : RelStructure.Embedding
      (wholeMaskTagExpansion (withPartsWholeMaskOld A partA))
      (wholeMaskTagExpansion (withPartsWholeMaskOld B partB)) :=
    (PartPreservingEmbedding.encode embPart).wholeMaskTag
  have hSame (x : U) : embTag x = j x := rfl
  have hOriginal :
      Source = wholeMaskTagExpansion (withPartsWholeMaskOld A partA) := by
    apply RelStructure.rel_injective
    funext R xs
    have hj := j.map_rel_iff R xs
    have hg := embTag.map_rel_iff R xs
    have heq : (embTag.toFun ∘ xs) = (j.toFun ∘ xs) := by
      funext i
      exact hSame (xs i)
    rw [heq] at hg
    exact propext (hj.symm.trans hg)
  rw [hOriginal]
  exact canonicalGenuineTagged2019Class_mem H A partA hA hTransA

end AllThoseRamseyClasses.Published
