import AllThoseRamseyClasses.Published.FunctionalWithParts2019CanonicalKClass
import PartiteConstruction.Functional.WholeMaskTaggedPartiteFaithful2019

/-!
# Canonical tagged K-membership is precisely original functional membership

The canonical tagged whole-mask representation of a finite transversal
partite genuine Option(Set) source remembers BOTH the entire function
(including none versus some-empty) and the part of every vertex.
Consequently, if the canonical tagged representation of (A,p)
belongs to a relational class defined as the image of a genuine
part-labelled functional class H, then (A,p) itself belongs to H;
there is no ambiguity from an unrelated functional presentation.

Combined with the checked 2019 local K-completion theorem, this
recovers a local completion target that is an ACTUAL member of the
original genuinely partial functional H class, while preserving the
exact weak source, source-defined partial map and full embeddings on
canonical protected tests. Relational K-local completion itself remains
an explicit independent hypothesis, not an outcome of the encoding.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V W T : Type w}

/-- Membership in a class of canonical tagged K-pictures reflects
EXACT membership of the decoded partial-function object in H.
No isomorphism-invariance premise is needed for SAME-CARRIER equality. -/
theorem canonicalGenuineTagged2019Class_reflect_mem
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    {X : Type w} [Finite X]
    (A : PartialSetStructure L X) (part : X → Parts)
    (hTr : FibreTransversal A part)
    (hK : canonicalGenuineTagged2019Class H
      (wholeMaskTagExpansion (withPartsWholeMaskOld A part))) :
    H A part := by
  obtain ⟨_, B, partB, hHB, hTrB, hEq⟩ := hK
  obtain ⟨hStructures, hParts⟩ :=
    withPartsWholeMaskTagged_injective B A partB part hTrB hTr hEq.symm
  simpa [hStructures, hParts] using hHB

/-- Equivalence of K-membership after full genuine functional
encoding, including part labels on isolated vertices. -/
theorem canonicalGenuineTagged2019Class_mem_iff
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    {X : Type w} [Finite X]
    (A : PartialSetStructure L X) (part : X → Parts)
    (hTr : FibreTransversal A part) :
    canonicalGenuineTagged2019Class H
      (wholeMaskTagExpansion (withPartsWholeMaskOld A part)) ↔
      H A part := by
  constructor
  · exact canonicalGenuineTagged2019Class_reflect_mem H A part hTr
  · intro hH
    exact canonicalGenuineTagged2019Class_mem H A part hH hTr

/-- Whenever the verified 2019 two-pass proof supplies a local
completion in the canonical relational K-image of H, its target
really belongs to ORIGINAL functional H and the same map carries
every surviving complete weak value plus all protected canonical
closed irreducible copies. No arbitrary intrinsic weak domain
reflection, and no enlargement of the tested S, is asserted. -/
theorem genuine2019_exactWeak_originalClass_completion
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (B : PartialSetStructure L W) (partB : W → Parts)
    (hClosed : IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {Y : Type w}
      (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Y),
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      RelStructure.Embedding Test C →
      Nonempty (RelStructure.Embedding Test
        (wholeMaskTagExpansion
          ((B.withParts partB).wholeMaskPatternGraph partB))))
    (S : Set V)
    (hCompletion : HasInducedClosedUKCompletion
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce S)) :
    ∃ (X : Type w) (_ : Finite X)
      (Target : PartialSetStructure L X) (targetPart : X → Parts),
        H Target targetPart ∧
        FibreTransversal Target targetPart ∧
        (wholeMaskTagExpansion
          (withPartsWholeMaskOld Target targetPart)).Irreducible ∧
        ∃ f : S → X,
          IsOriginalPartialHomomorphism
            (wholeWeakInduce (wholeMaskOriginalDecode C) S)
            Target f ∧
          (∀ x : S, targetPart (f x) =
            wholeMaskCoveredPart C B partB hClosed hCover x.1) ∧
          (∀ (A : PartialSetStructure L T) [Finite T]
            (partA : T → Parts),
            FibreTransversal A partA →
            IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts)
              (wholeMaskTagExpansion (withPartsWholeMaskOld A partA)) →
            ∀ e : RelStructure.Embedding
              (wholeMaskTagExpansion (withPartsWholeMaskOld A partA))
              (C.induce S),
              ∃ g : PartPreservingEmbedding A partA Target targetPart,
                ∀ x : T, g.1.toFun x = f (e x)) := by
  classical
  obtain ⟨X, hX, Target, targetPart, hTr, hTagK, hIrr,
      f, hPartial, hParts, hProtected⟩ :=
    functional2019_exactWeak_K_completion_of_canonical_targets
      (canonicalGenuineTagged2019Class H)
      (canonicalGenuineTagged2019Class_targetsCanonical H)
      C B partB hClosed hPos hCover S hCompletion
  letI : Finite X := hX
  have hH : H Target targetPart :=
    canonicalGenuineTagged2019Class_reflect_mem
      H Target targetPart hTr hTagK
  exact ⟨X, hX, Target, targetPart,
    hH, hTr, hIrr, f, hPartial, hParts, hProtected⟩

end AllThoseRamseyClasses.Published
