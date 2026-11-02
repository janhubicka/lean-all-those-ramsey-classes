import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeWeakDirection
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedCoveredParts
import AllThoseRamseyClasses.Published.FunctionalWithParts2019LocalProtectedCompletion

/-!
# Track C: exact ambient relative completion with genuine protected copies

The previous bridge produced an original-partial positive functional
homomorphism from the decoded weak source. This module also transports
the checked corrected-2019 CLOSED/IRREDUCIBLE canonical test protection,
with the *same local witness map*, and preserves the source's actual
unary part labels.

Significantly, no FIXED Base B-copy coverage is assumed. Under the
actual class-local condition (4b), the source's unary part map is
already available from the singleton U-hull theorem. Remaining
assumptions are displayed, notably OLD entire-value uniqueness.

Neither result upgrades arbitrary intrinsic whole-weak irreducible
tests, whose domain masks can change, to protected canonical OLD
tests. It is therefore a precise intermediate class-local bridge,
not yet the full original intrinsic functional local-finiteness axiom.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- An actual H-target and ONE genuine positive weak functional map
which preserves all assigned vertex parts AND every full canonical
closed U-irreducible test present in the ambient tagged weak source.
The tested source carrier S is never enlarged. -/
def HasGenuineIntrinsicWeakCanonicalProtectedCompletion
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (partC : V → Parts)
    (S : Set V) : Prop :=
  ∃ (X : Type w) (_ : Finite X)
    (Target : PartialSetStructure L X) (targetPart : X → Parts),
      H Target targetPart ∧ FibreTransversal Target targetPart ∧
      ∃ (f : S → X),
        IsOriginalPartialHomomorphism
          (wholeWeakInduce (wholeMaskOriginalDecode C) S)
          Target f ∧
        (∀ x : S, targetPart (f x) = partC x.1) ∧
        (∀ {T : Type w} [Finite T]
          (A : PartialSetStructure L T) (partA : T → Parts),
          FibreTransversal A partA →
          IsUIrreducible
            ((L.withParts Parts).wholeMaskClosureRules Parts)
            (wholeMaskTagExpansion (withPartsWholeMaskOld A partA)) →
          ∀ e : RelStructure.Embedding
            (wholeMaskTagExpansion (withPartsWholeMaskOld A partA))
            (C.induce S),
            ∃ g : PartPreservingEmbedding A partA Target targetPart,
              ∀ x : T, g.1.toFun x = f (e x))

/-- Exact SAME-map ambient-to-intrinsic transfer, with part labels and
full protection on canonical closed OLD tests. A complete-value
uniqueness condition is explicit; no source normalization is assumed. -/
theorem relative_implies_intrinsicWeakCanonicalProtected_of_unique
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (partC : V → Parts)
    (hPartC : ∀ x, WholeMaskVertexPartHolds C x (partC x))
    (S : Set V)
    (hUnique : HasUniqueWholeMaskValues (wholeMaskTagReduct C))
    (hRelative :
      HasGenuinePartiteTagged2019RelativeCompletion H (C.induce S)) :
    HasGenuineIntrinsicWeakCanonicalProtectedCompletion H C partC S := by
  rcases hRelative with
    ⟨X, hFinite, Target, targetPart, hH, hTr, _, f, hTagged⟩
  letI : Finite X := hFinite
  have hOld :
      ((wholeMaskTagReduct C).induce S).IsHomomorphism
        (withPartsWholeMaskOld Target targetPart) f := by
    intro R xs hR
    exact hTagged.1 (.inl R) xs hR
  have hPlus :
      IsOriginalPartialHomomorphism
        (wholeWeakInduce
          ((wholeMaskTagReduct C).wholeMaskPartialDecode) S)
        (Target.withParts targetPart) f :=
    wholeMaskPartialDecode_weak_originalPartial_of_inducedOldHom
      (wholeMaskTagReduct C) hUnique S
      (Target.withParts targetPart) targetPart f hOld
  have hWeak :
      IsOriginalPartialHomomorphism
        (wholeWeakInduce (wholeMaskOriginalDecode C) S)
        Target f := by
    constructor
    · intro R xs hR
      exact hPlus.1 (.inl (ULift.up R)) xs hR
    · intro F xs U hU
      exact hPlus.2 (ULift.up F) xs U hU
  have hParts (x : S) : targetPart (f x) = partC x.1 := by
    have hSource : (C.induce S).rel
        (.inl (.inl (.inr (partC x.1))))
        (fun _ : Fin 1 => x) := hPartC x.1
    have hMapped := hTagged.1
      (.inl (.inl (.inr (partC x.1))))
      (fun _ : Fin 1 => x) hSource
    exact hMapped
  have hProtected :
      ∀ {T : Type w} [Finite T]
        (A : PartialSetStructure L T) (partA : T → Parts),
        FibreTransversal A partA →
        IsUIrreducible
          ((L.withParts Parts).wholeMaskClosureRules Parts)
          (wholeMaskTagExpansion (withPartsWholeMaskOld A partA)) →
        ∀ e : RelStructure.Embedding
          (wholeMaskTagExpansion (withPartsWholeMaskOld A partA))
          (C.induce S),
          ∃ g : PartPreservingEmbedding A partA Target targetPart,
            ∀ x : T, g.1.toFun x = f (e x) := by
    intro T hT A partA hTransA hIrred e
    exact canonicalProtectedTest_of_closedULocalHE
      C S Target targetPart hTr f
      (IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hTagged)
      A partA hTransA hIrred e
  exact ⟨X, hFinite, Target, targetPart,
    hH, hTr, f, hWeak, hParts, hProtected⟩

/-- The actual corrected (4b) clause eliminates the extra arbitrary
vertex-part assignment used by the preceding bridge. This removes one
class-level source-normalization obligation without assuming fixed
B-copy coverage. The remaining complete-value-coherence hypothesis is
not silently discharged. -/
theorem correctedCovered_relative_implies_intrinsicWeakCanonicalProtected
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hUnique : HasUniqueWholeMaskValues (wholeMaskTagReduct C))
    (S : Set V)
    (hRelative :
      HasGenuinePartiteTagged2019RelativeCompletion H (C.induce S)) :
    HasGenuineIntrinsicWeakCanonicalProtectedCompletion
      H C (genuineTagged2019_correctedCoveredPart
        H C hClosed hCovered) S :=
  relative_implies_intrinsicWeakCanonicalProtected_of_unique
    H C
    (genuineTagged2019_correctedCoveredPart H C hClosed hCovered)
    (genuineTagged2019_correctedCoveredPart_holds
      H C hClosed hCovered)
    S hUnique hRelative

end AllThoseRamseyClasses.Published
