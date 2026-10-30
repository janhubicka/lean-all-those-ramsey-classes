import AllThoseRamseyClasses.Published.FunctionalWithParts2019CanonicalKClass
import AllThoseRamseyClasses.Published.InducedClosedLogicalDirection

/-!
# Exactly which functional weak completion axiom the corrected 2019 proof needs

Given a genuine part-labelled Option(Set) functional class H, define
its relational K as the EXACT canonical full-root-tagged images of H.
A candidate weak source is still the AMBIENT RELATIONAL structure
E.induce S, not the canonical tagged graph of the intrinsic whole-weak
functional restriction. The latter differs whenever a full function
value leaves S, by the verified domain-mask obstruction.

An ambient-relative genuine functional completion consists of an
actual finite H target T with transversal output fibres, together
with a corrected 2019 induced-closed U-homomorphism-embedding from
the ambient exact weak tagged source into the canonical graph of T.
The target's tagged graph is required to be irreducible.

We prove this is equivalent to an abstract 2019 K,U-completion
for the canonical tagged K class, preserving SAME weak source
vertices and K-target membership. We also rewrite the WHOLE fixed-
cutoff Definition 2.17(4) local-completion predicate in this honest
functional target form.

No new local-completion assumption is proved here! The theorem
precisely exposes the single remaining transfer required of any
original functional locally finite completion axiom. In particular,
it is not permissible to replace this relative condition by a
map that preserves only the defined operations of the intrinsic
weak functional restriction, or by closing the weak source.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V W Z : Type w}

/-- Exact relative weak completion, with the target in the ORIGINAL
part-labelled partial function class H and the map in the ambient
semi-closed OLD relational language (including persistent domain masks).
This is deliberately stronger than positive original partial
homomorphism of the intrinsic whole-fibre weak restriction. -/
def HasGenuinePartiteTagged2019RelativeCompletion
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V) :
    Prop :=
  ∃ (X : Type w) (_ : Finite X)
    (Target : PartialSetStructure L X) (targetPart : X → Parts),
      H Target targetPart ∧ FibreTransversal Target targetPart ∧
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld Target targetPart)).Irreducible ∧
      ∃ f : V → X, IsInducedClosedUHomomorphismEmbedding
        ((L.withParts Parts).wholeMaskClosureRules Parts)
        E (wholeMaskTagExpansion
          (withPartsWholeMaskOld Target targetPart)) f

/-- K-completions in the canonical image class are exactly genuine
functional ambient-relative completions. No quotient, hull or extra
closure state is inserted, and none/some-empty remain independent. -/
theorem canonicalGenuineTagged2019_KCompletion_iff_relative
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V) :
    HasInducedClosedUKCompletion
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) E ↔
    HasGenuinePartiteTagged2019RelativeCompletion H E := by
  classical
  constructor
  · rintro ⟨X, hX, D, hKD, hIrred, f, hf⟩
    letI : Finite X := hX
    obtain ⟨_, Target, targetPart, hH, hTr, hEq⟩ := hKD
    have hIrredCanonical :
        (wholeMaskTagExpansion
          (withPartsWholeMaskOld Target targetPart)).Irreducible := by
      rw [← hEq]
      exact hIrred
    have hfCanonical : IsInducedClosedUHomomorphismEmbedding
        ((L.withParts Parts).wholeMaskClosureRules Parts)
        E (wholeMaskTagExpansion
          (withPartsWholeMaskOld Target targetPart)) f := by
      rw [← hEq]
      exact hf
    exact ⟨X, hX, Target, targetPart, hH, hTr,
      hIrredCanonical, f, hfCanonical⟩
  · rintro ⟨X, hX, Target, targetPart, hH, hTr, hIrred, f, hf⟩
    letI : Finite X := hX
    exact ⟨X, hX,
      wholeMaskTagExpansion (withPartsWholeMaskOld Target targetPart),
      canonicalGenuineTagged2019Class_mem H Target targetPart hH hTr,
      hIrred, f, hf⟩

/-- The corrected 2019 locally finite completion axiom with ALL
small tests taken on their EXACT induced AMBIENT relational carriers,
but with completion witnesses stated as genuine functional H members. -/
def GenuinePartiteTagged2019LocalCompletionAt
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) W)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (n : ℕ) : Prop :=
  ∀ {X : Type w} [Finite X]
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
    IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C →
    (C0.Irreducible ∧ ∃ p : X → Z,
      IsInducedClosedUHomomorphismEmbedding
        ((L.withParts Parts).wholeMaskClosureRules Parts) C C0 p) →
    CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C →
    (∀ S : Finset X, S.card ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (↑S : Set X))) →
    HasCopywiseCompletion (canonicalGenuineTagged2019Class H) B C

/-- Exact equivalence with the corrected 2019 Definition 2.17(4)
for the image class H. The cutoff n, source C and every weak test
S are literally identical in both implications. Thus this theorem
isolates the remaining class-locality transfer without imposing the
false intrinsic weak full-embedding convention. -/
theorem canonicalGenuineTagged2019_localCompletion_iff_relative
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) W)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (n : ℕ) :
    InducedClosedULocalCompletionAt
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      B C0 n ↔
    GenuinePartiteTagged2019LocalCompletionAt H B C0 n := by
  constructor
  · intro h X hX C hClosed hProjection hCovered hSmall
    apply h C hClosed hProjection hCovered
    intro S hSize
    exact (canonicalGenuineTagged2019_KCompletion_iff_relative
      H (C.induce (↑S : Set X))).mpr (hSmall S hSize)
  · intro h X hX C hClosed hProjection hCovered hSmall
    apply h C hClosed hProjection hCovered
    intro S hSize
    exact (canonicalGenuineTagged2019_KCompletion_iff_relative
      H (C.induce (↑S : Set X))).mp (hSmall S hSize)

end AllThoseRamseyClasses.Published
