import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedIntrinsicLocalTransfer
import PartiteConstruction.Ramsey.CompletionTransfer

/-!
# Track C: an intrinsic FULL-weak local axiom can be vacuous

An arbitrary exact whole-fibre weak singleton need not fully embed
into ANY member of a class H, even when H consists of genuine
finite structures and is hereditary under genuine function-closed
restrictions.

If H has this singleton-obstruction uniformly, then a purported
functional local-finiteness condition whose small-test antecedent
demands FULL intrinsic weak H-completions is automatic at cutoff n=1:
no nonempty candidate can satisfy all the small-test premises.
For an empty candidate, the B-copywise conclusion is immediate
by mapping into the fixed class member B.

This is a precise LOGICAL WARNING, not a claim that any particular
non-Ramsey H has all the remaining multiamalgamation hypotheses.
Nor is this a refutation of the verified repaired ambient-relative
2019 theorem, whose local completion tests are different.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V W Z : Type w}

/-- A strong intrinsic weak-test completion: the genuine
whole-fibre partial function structure on the *same* carrier S
has a FULL embedding into an H member. No part-preservation is
required, making this notion weaker and its impossibility stronger
than the customary part-preserving variant. -/
def HasOriginalIntrinsicFullWeakHCompletion
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (A : PartialSetStructure L V) (S : Set V) : Prop :=
  ∃ (X : Type w) (_ : Finite X)
    (Target : PartialSetStructure L X) (partTarget : X → Parts),
      H Target partTarget ∧
      Nonempty (PartialSetStructure.Embedding (wholeWeakInduce A S) Target)

/-- No one-point whole-fibre weak restriction of any finite source
fully embeds in a member of H. This is intentionally strong and
independent of a chosen ambient tagged candidate. -/
def NoIntrinsicFullWeakSingletonHCompletions
    (H : GenuinePartite2019Class (L := L) (Parts := Parts)) : Prop :=
  ∀ {X : Type w} [Finite X]
    (A : PartialSetStructure L X) (x : X),
      ¬ HasOriginalIntrinsicFullWeakHCompletion H A {x}

/-- Exact cardinality: if a class uniformly forbids full weak
singleton H-completions, the premise requiring such completions for
ALL weak tests of at most n vertices forces the source empty as soon
as n >= 1. No closure enlargement, weakening to positive
homomorphisms, or missing distinctness assumptions enter. -/
theorem fullWeakAllSmall_forces_empty
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hNo : NoIntrinsicFullWeakSingletonHCompletions H)
    (A : PartialSetStructure L V) [Finite V]
    (n : ℕ) (hn : 1 ≤ n)
    (hSmall : ∀ S : Finset V, S.card ≤ n →
      HasOriginalIntrinsicFullWeakHCompletion H A (↑S : Set V)) :
    IsEmpty V := by
  classical
  refine ⟨fun x => ?_⟩
  have hOne : HasOriginalIntrinsicFullWeakHCompletion H A
      ({x} : Set V) := by
    have hSize : ({x} : Finset V).card ≤ n := by
      simpa using hn
    simpa using (hSmall {x} hSize)
  exact hNo A x hOne

/-- A candidate-level local axiom based on FULL intrinsic weak H
completions, retaining the *actual* corrected (4b), U-closedness,
ambient control and B-copywise conclusion. The original partial
function A is the decoded source on EXACTLY C's carrier.
This is stronger than the positive/canonical protected corrected
native hypothesis used by the proved Track C endpoint. -/
def GenuinePartiteIntrinsicFullWeakLocalCompletionAt
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
      HasOriginalIntrinsicFullWeakHCompletion
        H (wholeMaskOriginalDecode C) (↑S : Set X)) →
    HasCopywiseCompletion (canonicalGenuineTagged2019Class H) B C

/-- For a class with NO intrinsic FULL singleton weak completions,
the full-weak class-local implication at cutoff 1 holds AUTOMATICALLY
for EVERY canonical B member and EVERY control C0. It uses none of
the global control/coverage premises to reach the empty-source
conclusion. Thus this full-weak interpretation is not an adequate
unconditional replacement for the repaired ambient-relative axiom. -/
theorem intrinsicFullWeakLocalCompletionAt_one_of_noSingletons
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hNo : NoIntrinsicFullWeakSingletonHCompletions H)
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) W)
    (hB : canonicalGenuineTagged2019Class H B)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z) :
    GenuinePartiteIntrinsicFullWeakLocalCompletionAt H B C0 1 := by
  intro X hFinite C hClosed hControl hCovered hSmall
  letI : Finite X := hFinite
  have hEmpty : IsEmpty X :=
    fullWeakAllSmall_forces_empty H hNo
      (wholeMaskOriginalDecode C) 1 (by omega) hSmall
  letI : IsEmpty X := hEmpty
  let f : X → W := fun x => isEmptyElim x
  refine ⟨W, hB.1, B, hB, f, ?_⟩
  intro e
  exact ⟨Embedding.id B, fun b => isEmptyElim (e b)⟩

end AllThoseRamseyClasses.Published
