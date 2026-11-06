import AllThoseRamseyClasses.Published.FunctionalWithParts2019NativeKAssembledRamsey

/-!
# Appendix Track B: return from faithful genuine partial Ramsey to NATIVE Ramsey

The corrected 2019 two-pass Ramsey theorem now has a conditional
endpoint for H_K, the faithful original Option(Set) presentations of
ACTUAL transversal native functional partite K-systems.

The intended survey endpoint is nevertheless native: a full
part-preserving Ramsey witness in K in the original genuinely
set-valued function language. This module proves the final
same-carrier decoder. Full native partite embeddings are precisely
full part-preserving genuine partial embeddings between faithful
native presentations, and the equivalence respects COMPOSITION.
Consequently their true Ramsey arrows coincide.

The target from the genuine H_K Ramsey theorem is already guaranteed
by its exact H_K membership witness to be the faithful presentation
of a native K-system. No arbitrary intermediate tagged 2019 Picture
is decoded, and no nonclosed weak test is made into a full
substructure. Independent defined-empty operations are not
invented or forgotten.

All results below are conditional on the genuine partial Ramsey
hypothesis, and hence ultimately on the original global
ambient-relative local completion and ambient-host hypotheses
in the stacked 2019 theorem. They do NOT discharge Track C.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V W X : Type v}

/-- The EXACT identity-on-vertices correspondence between actual
FULL native function partite embeddings and FULL part-preserving
genuinely partial embeddings of their faithful representations.

The converse uses complete Option(Set) function value equations
to recover native full functional embeddings; a merely
source-defined original-partial map is insufficient.
Both directions preserve the actual part of every vertex. -/
noncomputable def nativePartiteFaithfulPartialEmbeddingEquiv
    (A : FunctionalPartite.System L Parts V)
    (B : FunctionalPartite.System L Parts W) :
    FunctionalPartite.Embedding A B ≃
      PartPreservingEmbedding
        A.toStructure.toNonemptyPartial A.part
        B.toStructure.toNonemptyPartial B.part where
  toFun e := ⟨e.toEmbedding.toNonemptyPartial, e.map_part⟩
  invFun e := {
    toEmbedding := {
      toFun := e.1.toFun
      injective := e.1.injective
      map_rel_iff := e.1.map_rel_iff
      map_func := by
        intro F xs
        have h := (e.1.toCollapsedNative).map_func F xs
        simpa only [Structure.toNonemptyPartial_collapseDomain] using h
    }
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
    apply PartialSetStructure.Embedding.ext
    intro x
    rfl

/-- Actual native full partite Ramsey arrows are equivalent to
genuine original-2019 partial-function part-preserving arrows
between the faithful objects on IDENTICAL carriers.

The proof tracks composition through the explicit equivalence.
No arity, finiteness, or completion assumption is used. -/
theorem nativePartiteArrow_iff_faithfulPartial
    (A : FunctionalPartite.System L Parts V)
    (B : FunctionalPartite.System L Parts W)
    (C : FunctionalPartite.System L Parts X)
    (κ : Type*) :
    FunctionalPartite.Arrow A B C κ ↔
      PartPreservingArrow
        A.toStructure.toNonemptyPartial A.part
        B.toStructure.toNonemptyPartial B.part
        C.toStructure.toNonemptyPartial C.part κ := by
  let φAB := nativePartiteFaithfulPartialEmbeddingEquiv A B
  let φBC := nativePartiteFaithfulPartialEmbeddingEquiv B C
  let φAC := nativePartiteFaithfulPartialEmbeddingEquiv A C
  have hNatural (g : FunctionalPartite.Embedding B C)
      (a : FunctionalPartite.Embedding A B) :
      φAC (g.comp a) = (φBC g).comp (φAB a) := by
    apply Subtype.ext
    apply PartialSetStructure.Embedding.ext
    intro x
    rfl
  constructor
  · intro h χ
    obtain ⟨b, hb⟩ := h (fun a => χ (φAC a))
    refine ⟨φBC b, ?_⟩
    intro a₁ a₂
    let a₁' := φAB.symm a₁
    let a₂' := φAB.symm a₂
    have he₁ : φAB a₁' = a₁ := φAB.apply_symm_apply a₁
    have he₂ : φAB a₂' = a₂ := φAB.apply_symm_apply a₂
    have hn₁ : φAC (b.comp a₁') = (φBC b).comp a₁ := by
      rw [← he₁]
      exact hNatural b a₁'
    have hn₂ : φAC (b.comp a₂') = (φBC b).comp a₂ := by
      rw [← he₂]
      exact hNatural b a₂'
    rw [← hn₁, ← hn₂]
    exact hb a₁' a₂'
  · intro h χ
    obtain ⟨b, hb⟩ := h (fun a => χ (φAC.symm a))
    let g : FunctionalPartite.Embedding B C := φBC.symm b
    refine ⟨g, ?_⟩
    intro a₁ a₂
    have hg : φBC g = b := φBC.apply_symm_apply b
    have hNat (a : FunctionalPartite.Embedding A B) :
        φAC (g.comp a) = b.comp (φAB a) := by
      rw [← hg]
      exact hNatural g a
    have hReflect (a : FunctionalPartite.Embedding A B) :
        φAC.symm (b.comp (φAB a)) = g.comp a := by
      apply φAC.injective
      simpa only [φAC.apply_symm_apply] using (hNat a).symm
    calc
      χ (g.comp a₁) =
          χ (φAC.symm (b.comp (φAB a₁))) :=
        congrArg χ (hReflect a₁).symm
      _ = χ (φAC.symm (b.comp (φAB a₂))) :=
        hb (φAB a₁) (φAB a₂)
      _ = χ (g.comp a₂) :=
        congrArg χ (hReflect a₂)

/-- The actual NATIVE partite Ramsey class property: for any two
FINITE genuine transversal partite K-systems A,B and a finite
nonempty colour type, find an actual native transversal target C
IN K satisfying the FULL function-language part-preserving arrow.
-/
def NativeKFinitePartiteRamsey2019
    (K : Structure.StructureClass.{u,v} (L := L)) : Prop :=
  ∀ {Y Z : Type v} [Finite Y] [Finite Z]
    (A : FunctionalPartite.System L Parts Y)
    (B : FunctionalPartite.System L Parts Z),
    K A.toStructure → K B.toStructure →
    ∀ (κ : Type) [Fintype κ] [Nonempty κ],
      ∃ (W : Type v) (_ : Finite W)
        (C : FunctionalPartite.System L Parts W),
        K C.toStructure ∧ FunctionalPartite.Arrow A B C κ

/-- A Ramsey theorem for the genuine faithful H_K partial class
automatically produces an ACTUAL native K partite Ramsey witness,
on the same target carrier and with FULL native partite embeddings.

The last stage does not decode arbitrary tagged relational
structures: H_K membership supplies the native target witness
directly, and the arrow equivalence preserves all compositions. -/
theorem nativeKFinitePartiteRamsey_of_faithful
    (K : Structure.StructureClass.{u,v} (L := L))
    (hH : GenuinePartite2019FiniteRamsey
      (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K)) :
    NativeKFinitePartiteRamsey2019 (Parts := Parts) K := by
  classical
  intro Y Z hY hZ A B hKA hKB κ hκ hκNonempty
  have hHA : nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K
      A.toStructure.toNonemptyPartial A.part :=
    ⟨A, hKA, rfl, rfl⟩
  have hHB : nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K
      B.toStructure.toNonemptyPartial B.part :=
    ⟨B, hKB, rfl, rfl⟩
  obtain ⟨W, hW, P, partP, hHP, hTransP, hArrow⟩ :=
    hH A.toStructure.toNonemptyPartial A.part
       B.toStructure.toNonemptyPartial B.part
       hHA hHB A.toNonemptyPartial_fibreTransversal
       B.toNonemptyPartial_fibreTransversal κ
  letI : Finite W := hW
  obtain ⟨C, hKC, hPEq, hPartEq⟩ := hHP
  subst P
  subst partP
  refine ⟨W, hW, C, hKC, ?_⟩
  exact (nativePartiteArrow_iff_faithfulPartial A B C κ).mpr hArrow

end AllThoseRamseyClasses.Published
