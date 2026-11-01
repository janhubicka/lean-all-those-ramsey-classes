import AllThoseRamseyClasses.Lifts.FiniteFamilyMarkedWitnessRamsey
import AllThoseRamseyClasses.Lifts.FiniteFamilyAmbientRelativeLocality

/-!
# Track E: the actual ordered Ramsey arrow from exact weak-local completions

Two independently kernel-checked results now fit exactly:

1. Bounded AMBIENT-RELATIVE completions of all literal weak
   native vertex subsets up to the forbidden-source size cutoff
   force genuine native forbidden EHN avoidance. This protects
   only full ambient irreducible tests and correct complete
   function fibres (not clipped weak-domain artefacts).
2. If a finite expanded control has a full ordered Ramsey arrow
   to an enlarged Bbar carrying an actual full maximizing
   native witness W_B of a marked B, and its native shadow is
   forbidden-free, the maximal folded induced trace on that
   shadow is an actual age member with the B Ramsey arrow.

The present theorem composes these without assuming native
forbidden avoidance separately. It is a precise terminal
CONDITIONAL Ramsey theorem whose only remaining construction
obligation is a sparse control C with an ordered ambient
Ramsey arrow and literal bounded ambient-relative weak-test
completions. It does NOT introduce an axiom, restate the
desired Ramsey property as a hypothesis, or claim that every
ambient Ramsey control has these completions.

The tagged Bbar and full witness compatibility are explicit
for now. A separate maximal-bar-witness construction and
order extension remove these presentation choices once their
independent CI checks pass. The original unrestricted regular
infinite-family distinct-root section remains separate.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Actual finite ordered maximal-trace Ramsey target from a
sparse finite control whose EXACT weak native subsets have
ambient-relative forbidden-free completions through one
chosen finite source-size cutoff.

All real function fibres are reflected on the final protected
B-copies; weak test maps are not presumed full or injective.
The theorem has no global native avoidance assumption: this
is derived from the verified finite-family locality result. -/
theorem finiteNamedMarkedWitnessRamsey_of_localCompletions
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VA VB VP VC VW : Type}
    [LinearOrder VA] [LinearOrder VB]
    [LinearOrder VP] [LinearOrder VC]
    [Finite VC]
    (A : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VA)
    (B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB)
    (Bbar : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VP)
    (C : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VC)
    (W : Structure L VW)
    (iW : Structure.Embedding (FiniteNamedTraceShadow Family B) W)
    (hMax : FiniteNamedCanonicalMaximalAlong Family
      (fun {U : Type} (E : Structure L U) =>
        FiniteNamedFiniteForbiddenFree Family E) iW)
    (hRel : ∀ (tag : Family.ComponentTag)
        (xs : Fin (tag.width Family) → VB),
        B.rel (.inr tag) xs ↔
          (finiteNamedClosedComponentFoldedLift Family W).rel
            (.inr tag) (iW ∘ xs))
    (mark : Structure.Embedding B.withLinearOrder Bbar.withLinearOrder)
    (wBar : Structure.Embedding W (FiniteNamedTraceShadow Family Bbar))
    (hMark : ∀ x : VB, wBar (iW x) = mark x)
    {κ : Type v} [Nonempty κ]
    (hArrow : Structure.Arrow A.withLinearOrder Bbar.withLinearOrder
      C.withLinearOrder κ)
    (n : ℕ)
    (hBound : ∀ i : Family.Index,
      Nat.card (Family.Carrier i) ≤ n)
    (hLocal : FiniteNamedAmbientRelativeWeakCompletions
      Family (FiniteNamedTraceShadow Family C) n) :
    ∃ (VT : Type) (_ : Finite VT) (o : LinearOrder VT)
      (T : Structure
        (functionalLiftLanguageBig L Family.ComponentTag
          (fun tag => tag.width Family)) VT),
      IsFiniteNamedMaximalTrace Family T ∧
      Structure.Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder _ VT T o.toLT) κ := by
  have hAvoid :
      AvoidsFiniteNamedEHN Family
        (FiniteNamedTraceShadow Family C) :=
    avoidsFiniteNamedEHN_of_ambientRelativeWeakCompletions
      Family (FiniteNamedTraceShadow Family C)
      n hBound hLocal
  exact finiteNamedMarkedWitnessRamsey_of_nativeAvoidance
    Family A B Bbar C W iW hMax hRel
    mark wBar hMark hArrow hAvoid

end AllThoseRamseyClasses.Lifts
