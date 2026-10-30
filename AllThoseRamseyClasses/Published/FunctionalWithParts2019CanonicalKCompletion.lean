import AllThoseRamseyClasses.Published.FunctionalWithParts2019LocalProtectedCompletion
import AllThoseRamseyClasses.Published.InducedClosed2019MainContract

/-!
# Functional local K-completion criterion with explicit canonical K-members

The constructed 2019 two-pass profile Ramsey picture already supplies
an induced-closed relational K-completion on EACH exact weak S.

A mathematically sufficient class condition for decoding this
completion is that EVERY relevant K-target on its actual carrier is
a canonical tagged complete-mask representation of a genuine
part-transversal Option(Set) partial-function object.

Under that extra class hypothesis, extracting the EXISTING
K-completion supplies a true source-defined original-partial
homomorphism of the decoded exact whole-fibre weak source, preserves
the actual vertex parts, and acts by full genuine partial-function
embeddings on ALL canonical closed U-irreducible tests that genuinely
occur as tagged substructures of the ambient induced weak source.

The finite weak carrier S, the B-covered final source, the actual
local K-target, and the cutoff n are unchanged.  K-target
irreducibility is retained.

This is a precise conditional SUFFICIENT criterion, NOT a proof
that the full 2019 relational multiamalgamation hypotheses
automatically make K canonical, and NOT full protection of
intrinsically irreducible whole-weak tests with lost domain bits.
The latter is obstructed by WholeMaskWeakDomainObstruction2019.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V W T : Type w}

/-- An EXPLICIT additional presentation property of a candidate
relational completion class: every finite K-member has a faithful
same-carrier genuinely partial, transversal source representation.
This is not inferred from U-closedness and strong amalgamation. -/
def All2019KTargetsCanonicalPartial
    (K : StructureClass
      (L := (L.withParts Parts).wholeMaskTagLanguage Parts)) : Prop :=
  ∀ {X : Type w} [Finite X]
    (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
    K E →
    ∃ (Target : PartialSetStructure L X) (targetPart : X → Parts),
      FibreTransversal Target targetPart ∧
      E = wholeMaskTagExpansion
        (withPartsWholeMaskOld Target targetPart)

/-- A corrected 2019 local exact induced K-completion can be decoded
as a genuine partial functional K-completion, and every protected
canonical closed U-irreducible test is mapped by a FULL embedding.

The conclusion keeps K-membership and irreducibility of the actual
canonical TAGGED target. It does NOT assert a full embedding of an
arbitrary intrinsically irreducible weak functional test. -/
theorem functional2019_exactWeak_K_completion_of_canonical_targets
    (K : StructureClass
      (L := (L.withParts Parts).wholeMaskTagLanguage Parts))
    (hKCanonical : All2019KTargetsCanonicalPartial K)
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
    (hCompletion : HasInducedClosedUKCompletion K
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce S)) :
    ∃ (X : Type w) (_ : Finite X)
      (Target : PartialSetStructure L X) (targetPart : X → Parts),
        FibreTransversal Target targetPart ∧
        K (wholeMaskTagExpansion
          (withPartsWholeMaskOld Target targetPart)) ∧
        (wholeMaskTagExpansion
          (withPartsWholeMaskOld Target targetPart)).Irreducible ∧
        ∃ f : S → X,
          IsOriginalPartialHomomorphism
            (wholeWeakInduce (wholeMaskOriginalDecode C) S)
            Target f ∧
          (∀ x : S,
            targetPart (f x) =
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
  obtain ⟨X, hX, E, hKE, hIrred, f, hf⟩ := hCompletion
  letI : Finite X := hX
  obtain ⟨Target, targetPart, hTrans, hCanonical⟩ :=
    hKCanonical E hKE
  have hCanK : K (wholeMaskTagExpansion
      (withPartsWholeMaskOld Target targetPart)) := by
    rw [← hCanonical]
    exact hKE
  have hCanIrred :
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld Target targetPart)).Irreducible := by
    rw [← hCanonical]
    exact hIrred
  have hCanMap : IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce S)
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld Target targetPart)) f := by
    rw [← hCanonical]
    exact hf
  obtain ⟨hPartial, hParts, hProtected⟩ :=
    genuineWithParts2019_exactWeak_local_canonical_protected
      C B partB hClosed hPos hCover S
      Target targetPart hTrans f hCanMap
  exact ⟨X, hX, Target, targetPart, hTrans,
    hCanK, hCanIrred, f, hPartial, hParts, hProtected⟩

end AllThoseRamseyClasses.Published
