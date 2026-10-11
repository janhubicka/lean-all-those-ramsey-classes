import AllThoseRamseyClasses.Published.EquivalencePushoutLabels

/-!
# A genuine equivalence relation on the paired free-amalgam carrier

No transitive closure is taken. The already constructed global
class-label map identifies precisely the common root E-classes and
keeps private left and private right classes distinct.

Equality of global labels is an equivalence relation whose
restrictions to the two embeddings are EXACTLY the original E
relations (both positive and negative tuples). Matching edges
are a subset of the new E relation.

This solves the E-part of the strong-amalgamation construction.
It does not yet supply a compatible total order.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Every finite or infinite paired span has a canonical-choice
E-completion on the actual strong free-amalgam vertex carrier,
and both side copies remain induced for this E relation. -/
theorem exists_equivalence_amalgam
    {D E F : Type}
    (Root : RelStructure Lang D)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (hRoot : pairedClass Root)
    (hLeft : pairedClass Left)
    (hRight : pairedClass Right)
    (sL : Embedding Root Left) (sR : Embedding Root Right) :
    ∃ Enew : FreeAmalgam.Vertex Root Left Right sL sR →
        FreeAmalgam.Vertex Root Left Right sL sR → Prop,
      Equivalence Enew ∧
      (∀ a b : E,
        Enew
          (FreeAmalgam.leftEmbedding Root Left Right sL sR a)
          (FreeAmalgam.leftEmbedding Root Left Right sL sR b) ↔
        edge Left .equiv a b) ∧
      (∀ a b : F,
        Enew
          (FreeAmalgam.rightEmbedding Root Left Right sL sR a)
          (FreeAmalgam.rightEmbedding Root Left Right sL sR b) ↔
        edge Right .equiv a b) := by
  classical
  obtain ⟨q, hL, hR⟩ :=
    exists_amalgam_E_labels Root Left Right hRoot hLeft hRight sL sR
  let Enew : FreeAmalgam.Vertex Root Left Right sL sR →
      FreeAmalgam.Vertex Root Left Right sL sR → Prop :=
    fun x y => q x = q y
  refine ⟨Enew, ?_, ?_, ?_⟩
  · constructor
    · intro x
      rfl
    · intro x y h
      exact h.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz
  · intro a b
    change q (FreeAmalgam.leftEmbedding Root Left Right sL sR a) =
      q (FreeAmalgam.leftEmbedding Root Left Right sL sR b) ↔
      edge Left .equiv a b
    rw [hL a, hL b]
    exact leftAmalgamTag_eq_iff Root Left Right hRoot hLeft hRight sL a b
  · intro a b
    change q (FreeAmalgam.rightEmbedding Root Left Right sL sR a) =
      q (FreeAmalgam.rightEmbedding Root Left Right sL sR b) ↔
      edge Right .equiv a b
    rw [hR a, hR b]
    exact rightAmalgamTag_eq_iff Root Left Right hRoot hLeft hRight sR a b

/-- The new E-relation also contains ALL matching edges of the
original concrete free amalgam. This uses only that each old side
satisfies M contained in E. -/
theorem exists_equivalence_amalgam_with_matching
    {D E F : Type}
    (Root : RelStructure Lang D)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (hRoot : pairedClass Root)
    (hLeft : pairedClass Left)
    (hRight : pairedClass Right)
    (sL : Embedding Root Left) (sR : Embedding Root Right) :
    ∃ Enew : FreeAmalgam.Vertex Root Left Right sL sR →
        FreeAmalgam.Vertex Root Left Right sL sR → Prop,
      Equivalence Enew ∧
      (∀ a b : E,
        Enew
          (FreeAmalgam.leftEmbedding Root Left Right sL sR a)
          (FreeAmalgam.leftEmbedding Root Left Right sL sR b) ↔
        edge Left .equiv a b) ∧
      (∀ a b : F,
        Enew
          (FreeAmalgam.rightEmbedding Root Left Right sL sR a)
          (FreeAmalgam.rightEmbedding Root Left Right sL sR b) ↔
        edge Right .equiv a b) ∧
      (∀ x y, edge (FreeAmalgam.amalgam Root Left Right sL sR)
        .mate x y → Enew x y) := by
  classical
  obtain ⟨Enew, hEquiv, hELeft, hERight⟩ :=
    exists_equivalence_amalgam Root Left Right hRoot hLeft hRight sL sR
  refine ⟨Enew, hEquiv, hELeft, hERight, ?_⟩
  intro x y hMate
  let hFree := FreeAmalgam.isFreeAmalgam Root Left Right sL sR
  have ht : (FreeAmalgam.amalgam Root Left Right sL sR).rel .mate ![x, y] :=
    hMate
  rcases (hFree.rel_iff .mate ![x, y]).mp ht with
      ⟨t, hM, hImage⟩ | ⟨t, hM, hImage⟩
  · have hx : x = FreeAmalgam.leftEmbedding Root Left Right sL sR (t 0) := by
      simpa using congrFun hImage 0
    have hy : y = FreeAmalgam.leftEmbedding Root Left Right sL sR (t 1) := by
      simpa using congrFun hImage 1
    rw [hx, hy]
    have hOld : edge Left .mate (t 0) (t 1) := by
      change Left.rel .mate ![t 0, t 1]
      have htup : t = ![t 0, t 1] := by
        funext k
        fin_cases k <;> rfl
      rw [← htup]
      exact hM
    exact (hELeft (t 0) (t 1)).mpr
      (hLeft.mate_equiv (t 0) (t 1) hOld)
  · have hx : x = FreeAmalgam.rightEmbedding Root Left Right sL sR (t 0) := by
      simpa using congrFun hImage 0
    have hy : y = FreeAmalgam.rightEmbedding Root Left Right sL sR (t 1) := by
      simpa using congrFun hImage 1
    rw [hx, hy]
    have hOld : edge Right .mate (t 0) (t 1) := by
      change Right.rel .mate ![t 0, t 1]
      have htup : t = ![t 0, t 1] := by
        funext k
        fin_cases k <;> rfl
      rw [← htup]
      exact hM
    exact (hERight (t 0) (t 1)).mpr
      (hRight.mate_equiv (t 0) (t 1) hOld)

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
