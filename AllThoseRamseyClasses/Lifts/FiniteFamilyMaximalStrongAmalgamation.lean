import AllThoseRamseyClasses.Lifts.FiniteFamilyCanonicalTrace
import PartiteConstruction.Functional.FullFreeAmalgam

/-!
# Genuine strong amalgamation of FINITE-family maximal canonical witnesses

The previous theorems provide two complementary ingredients:

1. Agreement of ALL component tags of A,B on a FULL common OLD root
   implies the true functional free amalgam of A,B avoids every
   forbidden weak EHN source from the finite named family.
2. If the canonical lift of A (resp. B) is maximal along its ENTIRE
   carrier, then any allowed full extension of A (resp. B) induces
   no new component tags on the original vertices, and hence the
   whole canonical trace embeds FULLY in its canonical lift.

Combining them with the independently verified concrete functional
free-amalgam constructor yields a true STRONG amalgam of the two
maximal canonical expanded witnesses: the lifted embeddings remain
injective, preserve all original partial functions and reflect every
new tag predicate, and the two images intersect precisely in the
given full OLD common root.

The expanded amalgam is the CANONICAL lift of an old free amalgam,
not necessarily a FREE amalgam in the expanded tag language:
additional cross-side tag relations can be present.

This is a substantial finite-family alternative to the hard step in
Section 3, conditional on MAXIMALITY of both input lifted witnesses
and agreement of their tag profiles on the overlap. Deriving a
complete hereditary age and its Ramsey theorem, and handling arbitrary
regular infinite forbidden families, remain separate obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The finite-family forbidden-free class in the original
functional language, with weak EHN homomorphism-embeddings. -/
abbrev FiniteNamedForbiddenFreeClass
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {W : Type} (A : Structure L W) : Prop :=
  AvoidsFiniteNamedEHN Family A

/-- A canonical finite-family lifted witness is *fully maximal*
if every allowed full extension preserves all canonical tag
predicates on its ENTIRE original finite carrier. -/
def FiniteNamedCanonicalFullyMaximal
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UA : Type} (A : Structure L UA) : Prop :=
  FiniteNamedCanonicalMaximalAlong
    Family (fun {W : Type} (C : Structure L W) =>
      FiniteNamedForbiddenFreeClass Family C)
    (Structure.Embedding.id A)

/-- The concrete functional free amalgam of two full native
structures carries both original structures into a single
forbidden-free shadow, and their canonical expanded FULL TRACE
embeddings are still full once the two witnesses are maximal.

The occurrence of the exact canonical tag profile agreement is
essential. Neither maximality alone nor agreement only of the old
functional root implies it. -/
theorem finiteNamedMaximalCanonicalLifts_strongAmalgam
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UX UA UB : Type}
    (X : Structure L UX)
    (Left : Structure L UA)
    (Right : Structure L UB)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hAgree : FiniteNamedComponentLiftsAgreeOn
      Family iLeft iRight)
    (hAvoidRight : FiniteNamedForbiddenFreeClass Family Right)
    (hMaxLeft : FiniteNamedCanonicalFullyMaximal Family Left)
    (hMaxRight : FiniteNamedCanonicalFullyMaximal Family Right) :
    ∃ (UT : Type) (Target : Structure L UT)
      (jLeft : Structure.Embedding Left Target)
      (jRight : Structure.Embedding Right Target),
      Structure.IsFreeAmalgam iLeft iRight jLeft jRight ∧
      FiniteNamedForbiddenFreeClass Family Target ∧
      ∃ (eLeft : Structure.Embedding
          (finiteNamedCanonicalTrace Family
            (Structure.Embedding.id Left))
          (finiteNamedClosedComponentFoldedLift Family Target))
        (eRight : Structure.Embedding
          (finiteNamedCanonicalTrace Family
            (Structure.Embedding.id Right))
          (finiteNamedClosedComponentFoldedLift Family Target)),
        (∀ a : UA, eLeft a = jLeft a) ∧
        (∀ b : UB, eRight b = jRight b) ∧
        (∀ a : UA, ∀ b : UB,
          eLeft a = eRight b ↔
            ∃ x : UX, a = iLeft x ∧ b = iRight x) := by
  classical
  let Target : Structure L
      (Structure.FreeAmalgam.Vertex
        X Left Right iLeft iRight) :=
    Structure.FreeAmalgam.amalgam X Left Right iLeft iRight
  let jLeft : Structure.Embedding Left Target :=
    Structure.FreeAmalgam.leftEmbedding
      X Left Right iLeft iRight
  let jRight : Structure.Embedding Right Target :=
    Structure.FreeAmalgam.rightEmbedding
      X Left Right iLeft iRight
  have hFree : Structure.IsFreeAmalgam
      iLeft iRight jLeft jRight :=
    Structure.FreeAmalgam.isFreeAmalgam
      X Left Right iLeft iRight
  have hAllowed : FiniteNamedForbiddenFreeClass Family Target :=
    finiteNamedAllComponentLift_freeAmalgam_avoids_of_agreement
      Family Target Left Right jLeft jRight X iLeft iRight
      hFree hAgree hAvoidRight
  let eLeft : Structure.Embedding
      (finiteNamedCanonicalTrace Family
        (Structure.Embedding.id Left))
      (finiteNamedClosedComponentFoldedLift Family Target) :=
    finiteNamedCanonicalTrace_into_allowed_extension Family
      (fun {W : Type} (C : Structure L W) =>
        FiniteNamedForbiddenFreeClass Family C)
      (Structure.Embedding.id Left) hMaxLeft
      Target hAllowed jLeft
  let eRight : Structure.Embedding
      (finiteNamedCanonicalTrace Family
        (Structure.Embedding.id Right))
      (finiteNamedClosedComponentFoldedLift Family Target) :=
    finiteNamedCanonicalTrace_into_allowed_extension Family
      (fun {W : Type} (C : Structure L W) =>
        FiniteNamedForbiddenFreeClass Family C)
      (Structure.Embedding.id Right) hMaxRight
      Target hAllowed jRight
  refine ⟨_, Target, jLeft, jRight, hFree,
    hAllowed, eLeft, eRight, ?_, ?_, ?_⟩
  · intro a
    rfl
  · intro b
    rfl
  · intro a b
    exact hFree.overlap a b

end AllThoseRamseyClasses.Lifts
