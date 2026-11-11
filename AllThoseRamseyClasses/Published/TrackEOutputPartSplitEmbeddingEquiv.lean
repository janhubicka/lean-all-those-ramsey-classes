import AllThoseRamseyClasses.Published.TrackESingletonWholeMaskNativeWeakBridge
import PartiteConstruction.Functional.OutputPartSingletonization

/-!
# Track E2: output-part splitting reflects FULL embeddings and Ramsey arrows

The pinned partite-construction library proves that full part-preserving
embeddings survive splitting each original set-valued function F into
singleton output-part functions (F,q). Here we prove the converse:
a FULL embedding between canonical split presentations preserves the
union of all original function fibres, and therefore reflects to a full
part-preserving embedding in the original language.

The bijection is on the same vertex maps and respects composition,
so the usual functional partite Ramsey arrow is equivalent on canonical
split objects. No extra vertices or closure hulls are introduced.

This is NOT an E2 local-completion constructor, a forbidden-class
comparison, or a proof that the 2019 sparse construction gives the
native ambient-relative weak HE. The irreducible-test clause remains
a separate obligation. Arbitrary noncanonical expanded-language
structures are outside the statement.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v}

/-- A FULL part-preserving embedding of canonical singleton-by-output-part
presentations preserves each entire original multivalued function fibre. -/
def systemEmbedding_of_splitOutputParts
    {VA VB : Type w}
    {A : FunctionalPartite.System L Parts VA}
    {B : FunctionalPartite.System L Parts VB}
    (e : FunctionalPartite.Embedding A.splitOutputParts B.splitOutputParts) :
    FunctionalPartite.Embedding A B where
  toEmbedding := {
    toFun := e
    injective := e.toEmbedding.injective
    map_rel_iff := by
      intro R xs
      exact e.toEmbedding.map_rel_iff (ULift.up R) xs
    map_func := by
      intro F xs
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hzSplit :
            z ∈ (A.splitOutputParts).func
              (ULift.up F, A.part z) xs := ⟨hz, rfl⟩
        have hzImage :
            e z ∈ imageSet e
              ((A.splitOutputParts).func (ULift.up F, A.part z) xs) :=
          ⟨z, hzSplit, rfl⟩
        rw [e.toEmbedding.map_func (ULift.up F, A.part z) xs] at hzImage
        exact hzImage.1
      · intro hy
        have hySplit :
            y ∈ (B.splitOutputParts).func
              (ULift.up F, B.part y) (e ∘ xs) := ⟨hy, rfl⟩
        have hyImage :
            y ∈ imageSet e
              ((A.splitOutputParts).func (ULift.up F, B.part y) xs) := by
          rw [e.toEmbedding.map_func (ULift.up F, B.part y) xs]
          exact hySplit
        obtain ⟨z, hz, hzy⟩ := hyImage
        exact ⟨z, hz.1, hzy⟩
  }
  map_part := e.map_part

/-- Canonical output-part singletonization provides a literal equivalence
of full partite copies, retaining their vertex maps. -/
def systemEmbedding_splitOutputPartsEquiv
    {VA VB : Type w}
    (A : FunctionalPartite.System L Parts VA)
    (B : FunctionalPartite.System L Parts VB) :
    FunctionalPartite.Embedding A B ≃
      FunctionalPartite.Embedding A.splitOutputParts B.splitOutputParts where
  toFun e := e.splitOutputParts
  invFun e := systemEmbedding_of_splitOutputParts e
  left_inv := by
    intro e
    apply FunctionalPartite.Embedding.ext
    intro x
    rfl
  right_inv := by
    intro e
    apply FunctionalPartite.Embedding.ext
    intro x
    rfl

/-- Correspondence of full copies commutes with composition. -/
theorem systemEmbedding_splitOutputParts_map_comp
    {VA VB VC : Type w}
    (A : FunctionalPartite.System L Parts VA)
    (B : FunctionalPartite.System L Parts VB)
    (C : FunctionalPartite.System L Parts VC)
    (g : FunctionalPartite.Embedding B C)
    (f : FunctionalPartite.Embedding A B) :
    systemEmbedding_splitOutputPartsEquiv A C (g.comp f) =
      (systemEmbedding_splitOutputPartsEquiv B C g).comp
        (systemEmbedding_splitOutputPartsEquiv A B f) := by
  apply FunctionalPartite.Embedding.ext
  intro x
  rfl

/-- Full partite Ramsey arrows are invariant under output-part
singletonization of all three canonical objects. This preserves
colourings on the SAME embedding spaces and handles arbitrary arities,
repeated inputs, nullary operations and multivalued original fibres. -/
theorem systemArrow_splitOutputParts_iff
    {VA VB VC : Type w}
    (A : FunctionalPartite.System L Parts VA)
    (B : FunctionalPartite.System L Parts VB)
    (C : FunctionalPartite.System L Parts VC)
    (κ : Type*) :
    FunctionalPartite.Arrow A B C κ ↔
      FunctionalPartite.Arrow
        A.splitOutputParts B.splitOutputParts C.splitOutputParts κ := by
  let ΦAB := systemEmbedding_splitOutputPartsEquiv A B
  let ΦBC := systemEmbedding_splitOutputPartsEquiv B C
  let ΦAC := systemEmbedding_splitOutputPartsEquiv A C
  have hNat (g : FunctionalPartite.Embedding B C)
      (f : FunctionalPartite.Embedding A B) :
      ΦAC (g.comp f) = (ΦBC g).comp (ΦAB f) :=
    systemEmbedding_splitOutputParts_map_comp A B C g f
  constructor
  · intro h χ
    obtain ⟨b, hb⟩ := h (fun a => χ (ΦAC a))
    refine ⟨ΦBC b, ?_⟩
    intro a₁ a₂
    let f₁ : FunctionalPartite.Embedding A B := ΦAB.symm a₁
    let f₂ : FunctionalPartite.Embedding A B := ΦAB.symm a₂
    have hf₁ : ΦAB f₁ = a₁ := ΦAB.apply_symm_apply a₁
    have hf₂ : ΦAB f₂ = a₂ := ΦAB.apply_symm_apply a₂
    have h1 : ΦAC (b.comp f₁) = (ΦBC b).comp a₁ := by
      rw [← hf₁]
      exact hNat b f₁
    have h2 : ΦAC (b.comp f₂) = (ΦBC b).comp a₂ := by
      rw [← hf₂]
      exact hNat b f₂
    rw [← h1, ← h2]
    exact hb f₁ f₂
  · intro h χ
    obtain ⟨b, hb⟩ := h (fun a => χ (ΦAC.symm a))
    let g : FunctionalPartite.Embedding B C := ΦBC.symm b
    refine ⟨g, ?_⟩
    intro f₁ f₂
    have hg : ΦBC g = b := ΦBC.apply_symm_apply b
    have hReflect (f : FunctionalPartite.Embedding A B) :
        ΦAC.symm (b.comp (ΦAB f)) = g.comp f := by
      apply ΦAC.injective
      simpa only [ΦAC.apply_symm_apply] using
        ((hNat g f).trans (by rw [hg])).symm
    calc
      χ (g.comp f₁) =
          χ (ΦAC.symm (b.comp (ΦAB f₁))) :=
            congrArg χ (hReflect f₁).symm
      _ = χ (ΦAC.symm (b.comp (ΦAB f₂))) :=
            hb (ΦAB f₁) (ΦAB f₂)
      _ = χ (g.comp f₂) :=
            congrArg χ (hReflect f₂)

end AllThoseRamseyClasses.Published
