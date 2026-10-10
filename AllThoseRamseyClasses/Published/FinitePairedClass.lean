import AllThoseRamseyClasses.Published.MatchingHereditary

/-!
# The genuinely finite counterexample class

The paper requires K to consist of FINITE U-closed structures.
The previously defined predicate \`pairedClass\` has no finiteness
condition; it is useful as a structural predicate on arbitrary carriers,
but it is not itself the finite class in Theorem 2.18.

This module explicitly imposes finite carriers and transfers the
verified closure, closed-hereditary and non-Ramsey conclusions.
No strong-amalgamation claim is smuggled into this wrapper.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The class in the handwritten Theorem 2.18 counterexample:
only finite ordered equivalence structures with a total matching. -/
abbrev finitePairedClass : StructureClass (L := Lang) :=
  fun {V} (C : RelStructure Lang V) => Finite V ∧ pairedClass C

theorem finiteA_mem : finitePairedClass A :=
  ⟨inferInstance, A_mem⟩

theorem finiteB_mem : finitePairedClass B :=
  ⟨inferInstance, B_mem⟩

/-- Every member of the finite class satisfies the actual matching
closure description, and hence Definition 2.17(1). -/
theorem finitePairedClass_isUClosed
    {V : Type} (C : RelStructure Lang V)
    (hC : finitePairedClass C) :
    IsUClosed mateRules C :=
  pairedClass_isUClosed C hC.2

/-- Published Definition 2.17(2), now for the finite carrier class. -/
theorem finitePairedClass_closedUHereditary :
    ClosedUHereditary finitePairedClass mateRules := by
  intro X Y A B hB hA e
  letI : Finite Y := hB.1
  have hX : Finite X :=
    Finite.of_injective e e.injective
  exact ⟨hX, pairedClass_of_closed_embedding A B hB.2 hA e⟩

/-- The exact literal Definition 2.17(4) for this FINITE class
holds at n=1. No part of the false ordinary-heredity property
is assumed, and C0 is an arbitrary control structure. -/
theorem finitePairedClass_literal_local_one
    {P : Type} (C0 : RelStructure Lang P) :
    LiteralULocalCompletionAt finitePairedClass mateRules B C0 1 := by
  have hNo :
      ∀ {X : Type} [Nonempty X] [Subsingleton X]
        (D : RelStructure Lang X), ¬ finitePairedClass D := by
    intro X _ _ D hD
    exact no_singleton_member D hD.2
  intro X hX C _ _ hTests _
  exact copywiseCompletion_of_intrinsic_tests_mem_of_no_singletons
    (K := finitePairedClass) B finiteB_mem C hNo hTests

/-- The finite class fails the Ramsey arrow for explicit A and B.
This does not assume that the desired witness is nonempty. -/
theorem finitePairedClass_has_no_B_Ramsey_witness :
    ¬ (∃ (V : Type) (_ : Finite V) (C : RelStructure Lang V),
      finitePairedClass C ∧ StructuralRamsey.Arrow A B C Bool) := by
  rintro ⟨V, hV, C, hC, hArrow⟩
  letI : Finite V := hV
  exact (no_finite_ramsey_witness C hC.2) hArrow

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
