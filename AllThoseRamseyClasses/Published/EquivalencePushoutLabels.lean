import AllThoseRamseyClasses.Published.EquivalenceGlobalLabels
import PartiteConstruction.Iterated.FreeAmalgam

/-!
# Glue compatible class labels across a genuine strong vertex pushout

The existing IsFreeAmalgam carries precisely the needed
set-theoretic pushout property: it covers the carrier by the two
embedded sides, and their images intersect exactly in the common
root. Consequently, any compatible pair of vertex labels has a
unique extension to the whole carrier.

This is the unbounded bridge from the quotient E-class labels to
the actual strong amalgam. It does NOT assume that the transitive
closure of E respects side embeddings.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

universe v

/-- The universal map-to-a-set property of a relational free
amalgam. No relation on the label type is needed. -/
theorem IsFreeAmalgam.exists_compatible_label
    {D E F P Q : Type v}
    {Root : RelStructure Lang D}
    {Left : RelStructure Lang E}
    {Right : RelStructure Lang F}
    {Whole : RelStructure Lang P}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (qL : E → Q) (qR : F → Q)
    (hCompat : ∀ d : D, qL (sL d) = qR (sR d)) :
    ∃ q : P → Q,
      (∀ a : E, q (iL a) = qL a) ∧
      (∀ b : F, q (iR b) = qR b) := by
  classical
  let Represents (z : P) (w : Q) : Prop :=
    (∃ a : E, z = iL a ∧ w = qL a) ∨
      (∃ b : F, z = iR b ∧ w = qR b)
  have hUnique (z : P) : ∃! w : Q, Represents z w := by
    obtain ⟨a, ha⟩ | ⟨b, hb⟩ := hFree.covers z
    · refine ⟨qL a, Or.inl ⟨a, ha, rfl⟩, ?_⟩
      intro w hw
      rcases hw with ⟨a', ha', rfl⟩ | ⟨b, hb, rfl⟩
      · have he : a = a' := iL.injective (ha.symm.trans ha')
        subst a'
        rfl
      · obtain ⟨d, haD, hbD⟩ :=
          (hFree.overlap a b).mp (ha.symm.trans hb)
        subst a
        subst b
        exact (hCompat d).symm
    · refine ⟨qR b, Or.inr ⟨b, hb, rfl⟩, ?_⟩
      intro w hw
      rcases hw with ⟨a, ha, rfl⟩ | ⟨b', hb', rfl⟩
      · obtain ⟨d, haD, hbD⟩ :=
          (hFree.overlap a b).mp (ha.symm.trans hb)
        subst a
        subst b
        exact hCompat d
      · have he : b = b' := iR.injective (hb.symm.trans hb')
        subst b'
        rfl
  let q : P → Q := fun z => Classical.choose (hUnique z)
  refine ⟨q, ?_, ?_⟩
  · intro a
    have h : Represents (iL a) (qL a) :=
      Or.inl ⟨a, rfl, rfl⟩
    exact ((Classical.choose_spec (hUnique (iL a))).2 (qL a) h).symm
  · intro b
    have h : Represents (iR b) (qR b) :=
      Or.inr ⟨b, rfl, rfl⟩
    exact ((Classical.choose_spec (hUnique (iR b))).2 (qR b) h).symm

/-- Specialize the universal pushout labelling to E-class labels.
Every root E-class is identified on both sides, and private
E-classes stay in distinct disjoint summands. -/
theorem exists_amalgam_E_labels
    {D E F : Type}
    (Root : RelStructure Lang D)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (hRoot : pairedClass Root)
    (hLeft : pairedClass Left)
    (hRight : pairedClass Right)
    (sL : Embedding Root Left) (sR : Embedding Root Right) :
    ∃ q : (FreeAmalgam.Vertex Root Left Right sL sR) →
        AmalgamClassLabels Root Left Right hRoot hLeft hRight,
      (∀ a : E, q (FreeAmalgam.leftEmbedding Root Left Right sL sR a) =
        leftAmalgamTag Root Left Right hRoot hLeft hRight sL a) ∧
      (∀ b : F, q (FreeAmalgam.rightEmbedding Root Left Right sL sR b) =
        rightAmalgamTag Root Left Right hRoot hLeft hRight sR b) := by
  classical
  exact IsFreeAmalgam.exists_compatible_label
    (FreeAmalgam.isFreeAmalgam Root Left Right sL sR)
    (leftAmalgamTag Root Left Right hRoot hLeft hRight sL)
    (rightAmalgamTag Root Left Right hRoot hLeft hRight sR)
    (amalgamTag_agree_on_root Root Left Right hRoot hLeft hRight sL sR)

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
