import AllThoseRamseyClasses.Published.PairedEquivalenceCycleObstruction
import AllThoseRamseyClasses.Published.FinitePairedClass
import PartiteConstruction.Ramsey.ClosureClosedLocalFiniteness

/-!
# Exact unbounded test needed to EXCLUDE paired equivalences from the
  coordinated repaired Definition 2.17(4)

This is the proof contract for the constructive finite E-cycle family.
The sole still-open task is the actual witness C_n for EVERY n. The
global non-completion is already a verified theorem in
PairedEquivalenceCycleObstruction, not a new assumption.

Crucially:
* control maps protect only U-CLOSED U-irreducible tests;
* membership (4b) tests precisely the same closed irreducibles;
* the local (4c) uses ALL original weak induced sets S with |S|<=n;
* there is NO commitment to the false (4b)-only correction;
* the source and control are exactly the original 2019 finite binary
  relational objects with the proposed coordinated map convention.

No class-level repaired Ramsey theorem is asserted here.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The precise input promised by the long E-cycle gadgets for
one fixed local cutoff n. The E-path/closing-negative pattern is
part of the data; B-copywise noncompletion follows from it. -/
def CoordinatedEPathBadWitnessAt
    {U P : Type}
    (Base : RelStructure Lang U)
    (Control : RelStructure Lang P)
    (n : ℕ) : Prop :=
  ∃ (V : Type) (_ : Finite V) (C : RelStructure Lang V),
    IsUClosed mateRules C ∧
    (Control.Irreducible ∧
      ∃ p : V → P,
        IsClosedUHomomorphismEmbedding mateRules C Control p) ∧
    ClosedUIrreduciblesIn finitePairedClass mateRules C ∧
    (∀ S : Finset V, S.card ≤ n →
      HasClosedUKCompletion finitePairedClass mateRules
        (C.induce (↑S : Set V))) ∧
    ∃ (m : ℕ) (backbone : ℕ → V),
      (∀ i : ℕ, i < m →
        PositiveCopyEdge Base C
          (backbone i) (backbone (i + 1))) ∧
      NegativeCopyEdge Base C (backbone 0) (backbone m)

/-- A checked E-path witness violates the repaired local-completion
implication at EXACTLY its cutoff n. All four antecedents are
retained; the non-completion is derived by transitivity, not
assumed. -/
theorem CoordinatedEPathBadWitnessAt.refutes_cutoff
    {U P : Type}
    (Base : RelStructure Lang U)
    (Control : RelStructure Lang P)
    (n : ℕ)
    (hBad : CoordinatedEPathBadWitnessAt Base Control n) :
    ¬ ClosedULocalCompletionAt finitePairedClass mateRules
        Base Control n := by
  intro hLocal
  obtain ⟨V, hV, C, hClosed, hProject, hCover, hSmall,
    m, backbone, hPath, hClosing⟩ := hBad
  letI : Finite V := hV
  have hCompletion : HasCopywiseCompletion finitePairedClass Base C :=
    hLocal C hClosed hProject hCover hSmall
  exact (no_K_copywise_completion_of_E_cycle
    Base C m backbone hPath hClosing) hCompletion

/-- The promised uniform-in-n family has the exact logical force
required to EXCLUDE K from the coordinated repaired class. No
claim is made that the family itself is already formalized. -/
theorem not_coordinated_local_completion_of_all_cutoffs
    {U P : Type}
    (Base : RelStructure Lang U)
    (Control : RelStructure Lang P)
    (hAll : ∀ n : ℕ,
      CoordinatedEPathBadWitnessAt Base Control n) :
    ¬ ∃ n : ℕ,
        ClosedULocalCompletionAt finitePairedClass mateRules
          Base Control n := by
  rintro ⟨n, hLocal⟩
  exact (CoordinatedEPathBadWitnessAt.refutes_cutoff
    Base Control n (hAll n)) hLocal

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
