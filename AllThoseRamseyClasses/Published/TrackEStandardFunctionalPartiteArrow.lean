import PartiteConstruction.Functional.TrackENativePartiteFinalArrow
import PartiteConstruction.Functional.Basic

/-!
# Track E: the new native part-preserving arrow IS the standard
# full-functional partite-System Ramsey arrow

The corrected 2019-to-native decoder yields
`NativePartPreservingArrow` on a Structure with an explicitly
recovered part map. The existing native Hales–Jewett machinery uses
`FunctionalPartite.System`, carrying independently checked
relational-tuple and function-fibre transversality fields. Those
full native System embeddings are exactly full Structure embeddings
with the identical part-preservation equation.

We prove a literal same-copy embedding equivalence and its
composition compatibility, then transport the Ramsey arrow.
No claim that an arbitrary final decoded target is already a
partite System: that requires BOTH transversality conditions,
which are being audited separately. Nor does this result
construct a new Ramsey witness.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.Structure.TrackENativePartiteFinalArrow

universe u v w
variable {L : Language.{u}} {Parts : Type v}

/-- Standard native partite embeddings are EXACTLY full functional
embeddings of their underlying Structures preserving all vertex part
labels, including isolated vertices. No choice of a different
embedding or change in source/target carrier. -/
def systemEmbedding_nativePartPreservingEquiv
    {VA VB : Type w}
    (A : FunctionalPartite.System L Parts VA)
    (B : FunctionalPartite.System L Parts VB) :
    FunctionalPartite.Embedding A B ≃
      NativePartPreservingEmbedding
        A.toStructure A.part B.toStructure B.part where
  toFun e := ⟨e.toEmbedding, e.map_part⟩
  invFun e := {
    toEmbedding := e.1
    map_part := e.2
  }
  left_inv := by
    intro e
    apply FunctionalPartite.Embedding.ext
    intro x
    rfl
  right_inv := by
    intro e
    apply Subtype.ext
    apply Structure.Embedding.ext
    intro x
    rfl

/-- The exact full A→B→C composition commutes with this native
system/Structure-plus-parts equivalence. This prevents losing the
monochromatic-copy equation while transferring Ramsey arrows. -/
theorem systemEmbedding_nativePartPreserving_map_comp
    {VA VB VC : Type w}
    (A : FunctionalPartite.System L Parts VA)
    (B : FunctionalPartite.System L Parts VB)
    (C : FunctionalPartite.System L Parts VC)
    (g : FunctionalPartite.Embedding B C)
    (f : FunctionalPartite.Embedding A B) :
    systemEmbedding_nativePartPreservingEquiv A C (g.comp f) =
      (systemEmbedding_nativePartPreservingEquiv B C g).comp
        (systemEmbedding_nativePartPreservingEquiv A B f) := by
  apply Subtype.ext
  apply Structure.Embedding.ext
  intro x
  rfl

/-- The original FunctionalPartite.Arrow definition and the new
native fully part-labelled Structure.Arrow formulation have
IDENTICAL quantified full A/B copies and colouring equations.
This is a true iff, not merely implication or an abstract
cardinality comparison. -/
theorem nativePartPreservingArrow_iff_standardSystemArrow
    {VA VB VC : Type w}
    (A : FunctionalPartite.System L Parts VA)
    (B : FunctionalPartite.System L Parts VB)
    (C : FunctionalPartite.System L Parts VC)
    (κ : Type*) :
    NativePartPreservingArrow
      A.toStructure A.part B.toStructure B.part
      C.toStructure C.part κ ↔
    FunctionalPartite.Arrow A B C κ := by
  let ΦAB := systemEmbedding_nativePartPreservingEquiv A B
  let ΦBC := systemEmbedding_nativePartPreservingEquiv B C
  let ΦAC := systemEmbedding_nativePartPreservingEquiv A C
  have hNat (g : FunctionalPartite.Embedding B C)
      (f : FunctionalPartite.Embedding A B) :
      ΦAC (g.comp f) = (ΦBC g).comp (ΦAB f) :=
    systemEmbedding_nativePartPreserving_map_comp A B C g f
  constructor
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

end AllThoseRamseyClasses.Published
