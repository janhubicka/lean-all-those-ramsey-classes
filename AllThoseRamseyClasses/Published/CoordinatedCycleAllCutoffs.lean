import AllThoseRamseyClasses.Published.CoordinatedCycleAllWeakCompletions
import AllThoseRamseyClasses.Published.CoordinatedCycleActualCopywiseObstruction
import AllThoseRamseyClasses.Published.CoordinatedCycleConcreteB0Gadgets
import AllThoseRamseyClasses.Published.CoordinatedNonlocalityCriterion
import AllThoseRamseyClasses.Published.OrderedAmbient

/-!
# Every cutoff of the coordinated 2019 local completion axiom fails

This is the exact end-to-end theorem target of the repair audit.
For every n we use the finite relational long cycle Cn with:

 - genuine U-closure for the original matching closure rule,
 - fixed 10-vertex irreducible control C0 and a closed-test
   preserving full positive homomorphism Cn -> C0 (4a),
 - every closed intrinsically U-irreducible induced test
   belongs to finite paired-equivalences K (4b),
 - EVERY exact weak substructure on <=n vertices has a
   genuine finite K completion by the amended closed-test map (4c),
 - genuine induced copies of fixed six-vertex B0 along the
   positive backbone and negative closing edge, forbidding
   all single-copywise K completions by E transitivity.

NO assumption in this file is the desired all-n existence:
we supply the actual explicit Cn, control projection,
copywise obstruction and all exact small-test completions.

This establishes that finite ordered paired equivalences fail the
COORDINATED closed-test local completion condition. It does NOT
establish the still-open positive Ramsey theorem under the new
definition, and it does not modify the literal published 2019
definition or the one-clause-only refuted repair.

This is a proposed Lean proof: certify only after full build and
permitted-axiom audit on the exact commit.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- A genuine concrete witness violating the local implication
at any specified n: all FOUR antecedents plus the true copywise
transitivity obstruction are proved from named finite structures. -/
theorem cycleGadgetWitness_bad_at_every_cutoff (n : ℕ) :
    CoordinatedEPathBadWitnessAt CycleBaseB0 CycleControlC0 n := by
  refine ⟨CycleVertex n, inferInstance, cycleGadgetWitness n,
    cycleGadgetWitness_isUClosed n, ?_, ?_, ?_, ?_⟩
  · have hCtrl : CycleControlC0.Irreducible :=
      orderedAmbient_irreducible CycleControlC0
        CycleControlC0_mem_ambient
    exact ⟨hCtrl, cycleControlVertex n,
      cycleGadgetWitness_control_closedEmbedding n⟩
  · exact cycleGadgetWitness_closedUIrreduciblesIn n
  · exact cycleGadgetWitness_all_weak_K_completions n
  · refine ⟨cycleBackboneCount n - 1,
      cycleBackboneRepresentative n,
      cycleGadgetWitness_positive_backbone_chain n, ?_⟩
    simpa only [cycleBackboneRepresentative_first,
      cycleBackboneRepresentative_last] using
        cycleGadgetWitness_closing_negativeCopyEdge n

/-- Concrete exclusion of the paired-equivalence class from the
coordinated locally finite completion property: no fixed cutoff
exists for the SAME fixed B0 and C0. -/
theorem finitePairedClass_no_coordinated_local_cutoff :
    ¬ ∃ n : ℕ,
      ClosedULocalCompletionAt finitePairedClass mateRules
        CycleBaseB0 CycleControlC0 n :=
  not_coordinated_local_completion_of_all_cutoffs
    CycleBaseB0 CycleControlC0
      cycleGadgetWitness_bad_at_every_cutoff

/-- The original paired-equivalence class, despite strong
amalgamation and failure of Ramsey, is NOT a multiamalgamation
class under the corrected coordinated 2019 closed-test definition.
This removes it as a counterexample to the revised hypotheses;
it does not prove the revised Ramsey implication. -/
theorem finitePairedClass_not_coordinated_multiamalgamation :
    ¬ ClosedUMultiamalgamationClass orderedAmbientClass
        finitePairedClass mateRules := by
  intro hPackage
  obtain ⟨n, hLocal⟩ :=
    hPackage.localCompletion CycleBaseB0 CycleControlC0
      CycleBaseB0_mem CycleControlC0_mem_ambient
  exact finitePairedClass_no_coordinated_local_cutoff
    ⟨n, hLocal⟩

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
