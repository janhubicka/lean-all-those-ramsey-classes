import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Functional.WholeMaskCoveredTaggedWeakLocalMap2019
import PartiteConstruction.Functional.WholeMaskCanonicalLocalProtectedTest2019

/-!
# Exact original-partial functional local maps from corrected 2019 K certificates

The verified 2019 two-pass profile construction gives a local
**induced-closed** U-homomorphism-embedding of the exact weak
ambient tagged OLD test into some K-member.  Here we assume that
the chosen K-target is CANONICALLY represented by an actual
partial Option(Set) structure with transversal output parts.

Two checked bridges then apply SIMULTANEOUSLY:

* the local map preserves the ENTIRE value of every surviving
  defined weak application, preserving some-empty versus none as
  source-defined partial-homomorphism semantics require;
* on every canonical U-closed U-irreducible genuine function test
  that actually fully embeds into the ambient exact weak tagged
  relational source, the SAME map restricts to a FULL, genuinely
  partial, part-preserving functional embedding.

The 2019 induced-test definition agrees with the reusable closed
embedded-test map condition, by the already verified normalization.

This does NOT assert arbitrary K-targets are canonical, nor that
every INTRINSIC irreducible whole-weak functional subtest lifts
fully into its AMBIENT induced OLD graph.  In fact the persistent
ambient domain-mask obstruction is a reason not to assume the
latter.  No source weak set is closed or enlarged.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V W X T : Type w}

/-- The corrected 2019 exact induced-closed local completion map
transfers to the original genuinely partial FUNCTION language
whenever the target is canonical; it additionally carries
all U-closed irreducible canonical TEST COPIES fully.
The theorem does not strengthen arbitrary K-member targets. -/
theorem genuineWithParts2019_exactWeak_local_canonical_protected
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
    (Target : PartialSetStructure L X) [Finite X]
    (targetPart : X → Parts)
    (hTransTarget : FibreTransversal Target targetPart)
    (f : S → X)
    (hLocal : IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce S)
      (wholeMaskTagExpansion (withPartsWholeMaskOld Target targetPart)) f) :
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
  have hWeak :=
    wholeMaskOriginalDecode_weak_originalPartial_of_taggedLocalHom
      C B partB hClosed hPos hCover S
      Target targetPart f hLocal.1
  refine ⟨hWeak.1, hWeak.2, ?_⟩
  intro A hFinite partA hTransA hIrred e
  exact canonicalProtectedTest_of_closedULocalHE
    C S Target targetPart hTransTarget f
    (IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hLocal)
    A partA hTransA hIrred e

end AllThoseRamseyClasses.Published
