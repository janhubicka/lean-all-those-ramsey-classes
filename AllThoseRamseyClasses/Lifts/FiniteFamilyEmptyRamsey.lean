import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceRamseyControl
import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceAge

/-!
# Track E regression: the empty finite forbidden family IS a Ramsey age

For a genuinely empty named forbidden family, the added folded
component-tag symbol type is empty. Thus every finite structure
in the expanded language is already a member of the maximal
induced-trace age: take its old shadow as its native witness
and the identity full embedding. Forbidden avoidance,
maximality of tag observations and reflection of every tag
are all vacuous because there are no named forbidden sources.

The all-arity functional EHN ordered Ramsey theorem then gives
an ACTUAL finite target belonging to the maximal-trace age.
This is an unconditional class-level ordered Ramsey theorem,
not a conditional transfer with a hidden completion hypothesis.

It verifies a useful boundary case of the proposed E2 construction:
no sparsening is needed if there are no native obstructions.
The general finite nonempty forbidden-family theorem remains
open, as does the original arbitrary regular infinite-family
Section 3 lift. All old partial/set-valued function fibres
and arbitrary nullary function arities are kept literally.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- When no named forbidden source exists, EVERY finite
expanded structure belongs to the alternative maximal-trace
age. The witness is precisely its native shadow, the witness
embedding is identity, and the tag-maximality predicates have
no possible indices. -/
theorem finiteNamedEmptyFamily_allFiniteTraces
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    [IsEmpty Family.Index]
    {V : Type} [Finite V]
    (Y : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) V) :
    IsFiniteNamedMaximalTrace Family Y := by
  let W : Structure L V := FiniteNamedTraceShadow Family Y
  let idW : Structure.Embedding W W := Structure.Embedding.id W
  have hAvoid : AvoidsFiniteNamedEHN Family W := by
    intro i f
    exact isEmptyElim i
  have hMax : FiniteNamedCanonicalMaximalAlong Family
      (fun {U : Type} (E : Structure L U) =>
        FiniteNamedFiniteForbiddenFree Family E) idW := by
    intro UC C hC e tag xs
    exact isEmptyElim tag.1
  refine ⟨inferInstance, V, W, inferInstance,
    hAvoid, idW, hMax, ?_⟩
  intro tag xs
  exact isEmptyElim tag.1

/-- An actual unconditional finite ORDERED Ramsey theorem
for the alternative finite-family maximal-trace age in the
boundary case of an empty forbidden family. No irreducibility,
source connectedness, positive function-arity or extra
embedding assumption is required. -/
theorem finiteNamedEmptyFamily_orderedRamsey
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    [IsEmpty Family.Index]
    {VA VB : Type}
    [Finite VA] [Finite VB]
    [LinearOrder VA] [LinearOrder VB]
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
      IsFiniteNamedMaximalTrace Family C ∧
      Structure.Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder _ VC C o.toLT) κ := by
  obtain ⟨VC, hFinC, o, C, hArrow⟩ :=
    finiteNamedTraceAmbient_orderedRamsey Family A B κ
  letI : Finite VC := hFinC
  exact ⟨VC, hFinC, o, C,
    finiteNamedEmptyFamily_allFiniteTraces Family C, hArrow⟩

end AllThoseRamseyClasses.Lifts
