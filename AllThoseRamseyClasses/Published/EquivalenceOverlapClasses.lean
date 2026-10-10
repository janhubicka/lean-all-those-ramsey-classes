import AllThoseRamseyClasses.Published.FinitePairedClass

/-!
# Equivalence-class compatibility on a strong-amalgamation overlap

For the paired-equivalence class, the future equivalence relation on
the free-amalgam carrier is obtained by identifying an E-class of the
left side with an E-class of the right side precisely when they share
an E-class of the common substructure.

The lemmas below prove the crucial uniqueness and compatibility:
different representatives of an E-class meeting the overlap
cannot induce different root E-classes. These are genuine
2019 relational EMBEDDING consequences; no closure operation or
quotient-class relabeling is assumed.

A global equivalence joining the two sides, with induced-restriction
proofs, is the remaining construction step and is not asserted here.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The equivalence relation is reflected on BOTH endpoints
of a full relational embedding, including its negative data. -/
theorem equivalence_embedding_iff
    {D X : Type}
    {Root : RelStructure Lang D} {Side : RelStructure Lang X}
    (s : Embedding Root Side) (a b : D) :
    edge Side .equiv (s a) (s b) ↔ edge Root .equiv a b := by
  have ht : s ∘ ![a, b] = ![s a, s b] := by
    funext i
    fin_cases i <;> rfl
  change Side.rel .equiv ![s a, s b] ↔
    Root.rel .equiv ![a, b]
  rw [← ht]
  exact s.map_rel_iff .equiv ![a, b]

/-- Two overlap vertices in the same side E-class were already
equivalent in the common root. This uses equivalence TRANSITIVITY
and full relation reflection; mere positive homomorphisms would
not suffice. -/
theorem root_class_unique_of_two_contacts
    {D X : Type}
    {Root : RelStructure Lang D} {Side : RelStructure Lang X}
    (hSide : pairedClass Side)
    (s : Embedding Root Side) (x : X) (d₁ d₂ : D)
    (h₁ : edge Side .equiv x (s d₁))
    (h₂ : edge Side .equiv x (s d₂)) :
    edge Root .equiv d₁ d₂ := by
  apply (equivalence_embedding_iff s d₁ d₂).mp
  exact hSide.equiv.trans (hSide.equiv.symm h₁) h₂

/-- Both side embeddings induce exactly the SAME equivalence
relation on the common root. Hence any crossing edge of the joined
equivalence is well-defined independently of its root representative. -/
theorem equivalence_agrees_on_overlap
    {D E F : Type}
    {Root : RelStructure Lang D}
    {Left : RelStructure Lang E} {Right : RelStructure Lang F}
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (d₁ d₂ : D) :
    edge Left .equiv (sL d₁) (sL d₂) ↔
      edge Right .equiv (sR d₁) (sR d₂) :=
  (equivalence_embedding_iff sL d₁ d₂).trans
    (equivalence_embedding_iff sR d₁ d₂).symm

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
