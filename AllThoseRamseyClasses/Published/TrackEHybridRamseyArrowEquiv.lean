import AllThoseRamseyClasses.Published.TrackEHybridFullEmbeddingEquiv
import PartiteConstruction.Ramsey.Basic

/-!
# Track E2: canonical hybrid FULL relational Ramsey arrow = native partite Ramsey arrow

The preceding full-faithful dictionary gives literal equivalences
of FULL embedding spaces, for canonical genuine finite partite
Systems, between native FUNCTIONAL embeddings and induced
relational embeddings in the combined original-OLD-mask/split-tag/
unary-part hybrid language.

These bijections are identity-on-vertices and commute with
composition. Hence ALL colouring arrows of three fixed native
partite Systems are equivalent to the standard relational
Ramsey arrows of their canonical hybrid presentations, with
the exact same colour type and without moving a vertex.

This is a semantic/embedding-category Ramsey-arrow transport:
it does NOT construct the relational hybrid Ramsey witness,
force arbitrary noncanonical intermediate tagged Pictures to decode
into a native function structure, or prove forbidden-family E2.

This proof uses the actual FULL native embedding spaces and never
substitutes source-defined homomorphism-embeddings or weak
projections, which have different function-domain reflection.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- For three finite genuine native functional partite Systems,
a Ramsey arrow using FULL native embeddings and parts is IFF
the ordinary induced relational embedding Ramsey arrow of the
canonical split/mask hybrid presentations. Exact source/target
carrier, colour type and vertex compositions are preserved. -/
theorem nativePartiteArrow_iff_canonicalSplitMaskHybridArrow
    {VA VB VC : Type w}
    [Finite VA] [Finite VB] [Finite VC]
    (A : FunctionalPartite.System L Parts VA)
    (B : FunctionalPartite.System L Parts VB)
    (C : FunctionalPartite.System L Parts VC)
    (κ : Type*) :
    FunctionalPartite.Arrow A B C κ ↔
      StructuralRamsey.Arrow
        A.splitMaskHybrid B.splitMaskHybrid C.splitMaskHybrid κ := by
  classical
  let ΦAB := nativePartiteHybridFullEmbeddingEquiv A B
  let ΦBC := nativePartiteHybridFullEmbeddingEquiv B C
  let ΦAC := nativePartiteHybridFullEmbeddingEquiv A C
  have hNatural (g : FunctionalPartite.Embedding B C)
      (a : FunctionalPartite.Embedding A B) :
      ΦAC (g.comp a) = (ΦBC g).comp (ΦAB a) := by
    apply RelStructure.Embedding.ext
    intro x
    rfl
  constructor
  · intro h χ
    obtain ⟨b, hb⟩ := h (fun a => χ (ΦAC a))
    refine ⟨ΦBC b, ?_⟩
    intro a₁ a₂
    let a₁' : FunctionalPartite.Embedding A B := ΦAB.symm a₁
    let a₂' : FunctionalPartite.Embedding A B := ΦAB.symm a₂
    have he₁ : ΦAB a₁' = a₁ := ΦAB.apply_symm_apply a₁
    have he₂ : ΦAB a₂' = a₂ := ΦAB.apply_symm_apply a₂
    have hn₁ : ΦAC (b.comp a₁') = (ΦBC b).comp a₁ := by
      rw [← he₁]
      exact hNatural b a₁'
    have hn₂ : ΦAC (b.comp a₂') = (ΦBC b).comp a₂ := by
      rw [← he₂]
      exact hNatural b a₂'
    rw [← hn₁, ← hn₂]
    exact hb a₁' a₂'
  · intro h χ
    obtain ⟨b, hb⟩ := h (fun a => χ (ΦAC.symm a))
    let g : FunctionalPartite.Embedding B C := ΦBC.symm b
    refine ⟨g, ?_⟩
    intro a₁ a₂
    have hg : ΦBC g = b := ΦBC.apply_symm_apply b
    have hNat (a : FunctionalPartite.Embedding A B) :
        ΦAC (g.comp a) = b.comp (ΦAB a) := by
      rw [← hg]
      exact hNatural g a
    have hReflect (a : FunctionalPartite.Embedding A B) :
        ΦAC.symm (b.comp (ΦAB a)) = g.comp a := by
      apply ΦAC.injective
      simpa only [ΦAC.apply_symm_apply] using (hNat a).symm
    calc
      χ (g.comp a₁) =
          χ (ΦAC.symm (b.comp (ΦAB a₁))) :=
        congrArg χ (hReflect a₁).symm
      _ = χ (ΦAC.symm (b.comp (ΦAB a₂))) :=
        hb (ΦAB a₁) (ΦAB a₂)
      _ = χ (g.comp a₂) :=
        congrArg χ (hReflect a₂)

end AllThoseRamseyClasses.Published
