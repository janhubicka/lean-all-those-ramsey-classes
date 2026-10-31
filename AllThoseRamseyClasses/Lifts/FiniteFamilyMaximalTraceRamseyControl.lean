import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceAge
import PartiteConstruction.Ramsey.FreeAmalgamationFunctionsAllArity

/-!
# Track E: a genuine finite ordered Ramsey control in the lift language

The enlarged language contains the ORIGINAL relations and all old
set-valued partial function symbols plus one relation symbol for
each finite named all-closed-component tag.

The class of ALL structures in this enlarged language is closed
under full functional free amalgamation. This holds with arbitrary
old function arities, including nullary functions; no extra
constraint on the added tag predicates is used.

The verified functional EHN theorem therefore provides an actual
finite ordered Ramsey control for any two finite structures in
this language, including two members of the finite maximal-trace
age. We do NOT assert that the control belongs to the age.

The remaining Track E theorem must take such a control, perform
the corrected multiamalgamation sparsening/local completion, and
produce a maximal-trace target preserving all ordered B-copies.
The existing strong amalgamation and finite fibres do NOT supply
that completion automatically.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- The total class of structures in the finite-family extended
language is a genuine FULL functional free-amalgamation class.
This does not say that the maximal-trace subage is free. -/
theorem finiteNamedTraceAmbient_freeAmalgamation
    (Family : FiniteNamedFunctionalSources.{u,0} L) :
    Structure.FreeAmalgamationClass
      (fun {V : Type}
        (_ : Structure
          (functionalLiftLanguageBig L Family.ComponentTag
            (fun tag => tag.width Family)) V) => True) := by
  constructor
  · intros
    trivial
  · intros
    trivial

/-- An unconditional, actually finite, ordered Ramsey control C0 in
the full finite-family lift LANGUAGE. The control need not be a trace
of a forbidden-free native structure.

This proves E1 independently of the local-completion and Claim 2
workstreams. Both external orders are the designated orders used by
the full-embedding Ramsey arrows. -/
theorem finiteNamedTraceAmbient_orderedRamsey
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VA VB : Type} [LinearOrder VA] [LinearOrder VB]
    [Finite VA] [Finite VB]
    (A : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VA)
    (B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB)
    (κ : Type v) [Fintype κ] [Nonempty κ] :
    ∃ (VC : Type) (_ : Finite VC) (o : LinearOrder VC)
      (C : Structure
        (functionalLiftLanguageBig L Family.ComponentTag
          (fun tag => tag.width Family)) VC),
      Structure.Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder _ VC C o.toLT) κ := by
  obtain ⟨VC, hVC, o, C, _, hArrow⟩ :=
    StructuralRamsey.Rooted.Structure.FreeAmalgamationClass.orderedRamsey_allArity
      (finiteNamedTraceAmbient_freeAmalgamation Family)
      A B True.intro True.intro κ
  exact ⟨VC, hVC, o, C, hArrow⟩

end AllThoseRamseyClasses.Lifts
