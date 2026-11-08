import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedWeakCanonical
import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeKCompletion
import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization

/-!
# Track C: irreducible weak tests require no separate local-completion premise

The exact canonical weak-irreducible target lemma already obtains a FULL
relational embedding of each ordinary irreducible exact induced weak test
C.induce S into a genuine part-labelled H structure, using corrected (4b)
and the ambient U-closedness of C.

When all canonical H targets are ordinary irreducible (as follows from
K(H) being included in an ambient class R of irreducible structures),
this full embedding is itself an induced-closed U-homomorphism-embedding
and therefore an ambient-relative genuine H-completion on exactly S.

As a result, the corrected 2019 local-completion axiom can equivalently
test only those exact small sets S whose induced ambient source is
ordinary REDUCIBLE. Its cutoff n and global candidate C are unchanged.
This is a class-local quantifier reduction, not the missing intrinsic
weak-test => ambient-relative completion theorem for reducible tests.

The arbitrary original intrinsic weak completion condition may be vacuous,
and none of the results here identifies the intrinsic weak domain mask with
the ambient OLD mask. The finite tuple S is never replaced by its hull;
an auxiliary hull occurs only inside the previously verified canonical
target lemma.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w

variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V W Z : Type w}

/-- Under the ambient irreducibility hypothesis on the canonical K(H)
image, corrected (4b) already gives a *genuine H-valued ambient-relative*
completion for every ordinary irreducible exact weak test, independently
of any local-finiteness premise.

The map is the actual full induced relational embedding of C.induce S
into the canonical H target; no set enlargement or intrinsic weak
operation-domain substitution takes place. -/
theorem genuineTagged2019_weakIrred_has_relativeCompletion
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hKIrred : ∀ {X : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H E → E.Irreducible)
    (S : Set V) (hIrred : (C.induce S).Irreducible) :
    HasGenuinePartiteTagged2019RelativeCompletion H (C.induce S) := by
  classical
  obtain ⟨X, hFinite, Target, partTarget, hH, hTrans, ⟨e⟩⟩ :=
    genuineTagged2019_correctedCovered_weakIrred_canonicalTarget
      H C hClosed hCovered S hIrred
  letI : Finite X := hFinite
  have hK :
      canonicalGenuineTagged2019Class H
        (wholeMaskTagExpansion
          (withPartsWholeMaskOld Target partTarget)) :=
    canonicalGenuineTagged2019Class_mem H Target partTarget hH hTrans
  have hTargetIrred :
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld Target partTarget)).Irreducible :=
    hKIrred _ hK
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  have hMap :
      IsInducedClosedUHomomorphismEmbedding rules
        (C.induce S)
        (wholeMaskTagExpansion
          (withPartsWholeMaskOld Target partTarget)) e.toFun :=
    IsClosedUHomomorphismEmbedding.toInducedClosed
      (e.isClosedUHomomorphismEmbedding rules)
  exact ⟨X, hFinite, Target, partTarget, hH, hTrans,
    hTargetIrred, e.toFun, hMap⟩

/-- The corrected 2019 candidate-local axiom with its small-test
completion premise demanded only for ordinary REDUCIBLE exact weak
tests. It retains the original candidate, U-closedness, corrected
U-irreducible coverage (4b), ambient control map, cutoff and copywise
conclusion without replacing the tested S by an ambient closure. -/
def GenuinePartiteTagged2019ReducibleTestLocalCompletionAt
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
      ¬ (C.induce (↑S : Set X)).Irreducible →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (↑S : Set X))) →
    HasCopywiseCompletion (canonicalGenuineTagged2019Class H) B C

/-- On an irreducible canonical ambient class, checking all weak
local-completion premises in (4c) is EQUIVALENT to checking only
reducible exact weak tests. The original cutoff n and B,C0 are fixed. -/
theorem genuineTagged2019_localCompletion_iff_reducibleTests
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) W)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (n : ℕ)
    (hKIrred : ∀ {X : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H E → E.Irreducible) :
    GenuinePartiteTagged2019LocalCompletionAt H B C0 n ↔
      GenuinePartiteTagged2019ReducibleTestLocalCompletionAt
        H B C0 n := by
  constructor
  · intro hLocal X hX C hClosed hControl hCovered hReducible
    apply hLocal C hClosed hControl hCovered
    intro S hSize
    by_cases hIrred : (C.induce (↑S : Set X)).Irreducible
    · exact genuineTagged2019_weakIrred_has_relativeCompletion
        H C hClosed hCovered hKIrred (↑S : Set X) hIrred
    · exact hReducible S hSize hIrred
  · intro hReducible X hX C hClosed hControl hCovered hAll
    apply hReducible C hClosed hControl hCovered
    intro S hSize _
    exact hAll S hSize

/-- Under the original corrected theorem's ambient assumptions,
irreducibility of canonical K(H) follows from K(H) ⊆ R and
irreducibility of every R-member. No new class assumption is needed. -/
theorem genuineTagged2019_localCompletion_iff_reducibleTests_of_ambient
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (R : StructureClass
      (L := (L.withParts Parts).wholeMaskTagLanguage Parts))
    (hRIrred : ∀ {X : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      R E → E.Irreducible)
    (hSub : ∀ {X : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H E → R E)
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) W)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (n : ℕ) :
    GenuinePartiteTagged2019LocalCompletionAt H B C0 n ↔
      GenuinePartiteTagged2019ReducibleTestLocalCompletionAt
        H B C0 n :=
  genuineTagged2019_localCompletion_iff_reducibleTests H B C0 n
    (fun E hK => hRIrred E (hSub E hK))

end AllThoseRamseyClasses.Published
