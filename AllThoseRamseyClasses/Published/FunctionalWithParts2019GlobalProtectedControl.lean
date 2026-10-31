import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Functional.WholeMaskCoveredFunctionalControlProjection2019
import PartiteConstruction.Functional.WholeMaskCanonicalLocalProtectedTest2019

/-!
# True full functional copies under corrected 2019 global control maps

The final profile sparse Picture C has a corrected induced-closed
U-homomorphism-embedding into an ACTUAL canonical genuine partial
function control target C0. The verified whole-mask decoder already
turns its positive part into a source-defined original partial
homomorphism with recovered vertex parts.

This file additionally transfers the protected full-copy clause:
every genuinely partial canonical U-closed U-irreducible test whose
FULL tagged graph embeds in C maps to the control target by a FULL
part-preserving genuine Option(Set) embedding on the SAME vertex map.

Thus the global control has the exact corrected 2019 protected-copy
strength, without claiming it reflects arbitrary intrinsically weak
(nonclosed) functional domains. The latter is blocked by the
verified finite unary example. No extra closure hull is introduced.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V W T Z : Type w}

/-- The corrected 2019 GLOBAL induced-closed map to a CANONICAL
target restricts to a full genuinely partial part-preserving
embedding on any actually embedded canonical closed U-irreducible
tagged test. No final B-copy coverage assumption is needed here. -/
theorem genuine2019_global_protected_canonical_copy
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (Target : PartialSetStructure L W) [Finite W]
    (targetPart : W → Parts)
    (hTransTarget : FibreTransversal Target targetPart)
    (f : V → W)
    (hTag : IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      C (wholeMaskTagExpansion (withPartsWholeMaskOld Target targetPart)) f)
    (A : PartialSetStructure L T) [Finite T]
    (partA : T → Parts)
    (hTransA : FibreTransversal A partA)
    (hIrr : IsUIrreducible
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (wholeMaskTagExpansion (withPartsWholeMaskOld A partA)))
    (e : RelStructure.Embedding
      (wholeMaskTagExpansion (withPartsWholeMaskOld A partA)) C) :
    ∃ g : PartPreservingEmbedding A partA Target targetPart,
      ∀ x : T, g.1.toFun x = f (e x) := by
  classical
  have hTrPlus : FibreTransversal (A.withParts partA) partA :=
    (A.withParts_fibreTransversal_iff partA).mpr hTransA
  have hTestClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (wholeMaskTagExpansion (withPartsWholeMaskOld A partA)) :=
    (A.withParts partA).wholeMaskTagExpansion_isUClosed
      partA hTrPlus
  obtain ⟨gTag, hgTag⟩ :=
    (IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hTag).on_test
      (wholeMaskTagExpansion (withPartsWholeMaskOld A partA))
      hTestClosed hIrr e
  let gOld : RelStructure.Embedding
      (withPartsWholeMaskOld A partA)
      (withPartsWholeMaskOld Target targetPart) :=
    gTag.wholeMaskTagReduct
  refine ⟨PartPreservingEmbedding.decode hTransA hTransTarget gOld, ?_⟩
  intro x
  change gTag x = f (e x)
  exact hgTag x

/-- Assemble the VERIFIED final B-covered decoder's actual
source-defined global partial homomorphism and vertex part control
WITH every full genuinely partial protected canonical test copy
of the corrected 2019 global induced-closed map. -/
theorem genuine2019_global_control_and_protected_functional_copies
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (Base : PartialSetStructure L Z) (basePart : Z → Parts)
    (hC : IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {Y : Type w}
      (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Y),
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      RelStructure.Embedding Test C →
      Nonempty (RelStructure.Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (Target : PartialSetStructure L W) [Finite W]
    (targetPart : W → Parts)
    (hTransTarget : FibreTransversal Target targetPart)
    (f : V → W)
    (hTag : IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      C (wholeMaskTagExpansion (withPartsWholeMaskOld Target targetPart)) f) :
    IsOriginalPartialHomomorphism
      (wholeMaskOriginalDecode C) Target f ∧
    (∀ x : V,
      targetPart (f x) = wholeMaskCoveredPart C Base basePart hC hCover x) ∧
    (∀ (A : PartialSetStructure L T) [Finite T]
      (partA : T → Parts),
      FibreTransversal A partA →
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts)
        (wholeMaskTagExpansion (withPartsWholeMaskOld A partA)) →
      ∀ e : RelStructure.Embedding
        (wholeMaskTagExpansion (withPartsWholeMaskOld A partA)) C,
        ∃ g : PartPreservingEmbedding A partA Target targetPart,
          ∀ x : T, g.1.toFun x = f (e x)) := by
  have hSource :=
    wholeMaskOriginalDecode_originalPartialControl_of_tagHom
      C Base basePart hC hPos hCover
      Target targetPart f hTag.1
  refine ⟨hSource.1, hSource.2, ?_⟩
  intro A hFinite partA hTrA hIrr e
  exact genuine2019_global_protected_canonical_copy
    C Target targetPart hTransTarget f hTag
    A partA hTrA hIrr e

end AllThoseRamseyClasses.Published
