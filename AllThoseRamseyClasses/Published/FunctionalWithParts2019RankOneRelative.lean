import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedWeakCanonical
import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeKCompletion
import PartiteConstruction.Ramsey.ClosureRankOneBase

/-!
# Track C: rank-one U-closed completions and exact weak singleton completions

This is the genuinely elementary base of the corrected 2019
local-completion problem, formalized directly from merged source
lemmas. No rank increment, source-hull extension oracle, strict
functional B-tree theorem, or fixed B-cover is assumed.

If every canonical K(H)-member is ORDINARY irreducible, then
corrected (4b) gives a genuine H-relative completion of every
U-closed induced test with U-size <= 1. Indeed, the existing
rank-one base lemma makes such a test U-irreducible, so (4b)
puts it into K(H) already; the identity is a complete local
map to that very target.

More strongly, an exact weak induced test with <=1 VERTEX is
ordinary irreducible, even if it is not U-closed. The verified
canonical weak-irreducible target lemma from (4b) embeds it
fully into a genuine canonical H-target, and a full embedding
is automatically a corrected relative 2019 completion map.

This all-weak rank-one completion needs NO positive function arity,
test closure, global H membership or extra target vertices in
the SOURCE. The target may be larger. Its irreducibility assumption
is the same ambient class-irreducibility condition already present
in the conditional functional Ramsey theorem.

It does not solve the higher-rank U-reducible completion/gluing
problem or assert any equivalence for full intrinsic whole-weak
functional embeddings.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V W Z : Type w}

/-- The exact irreducibility premise used in 2019 canonical H-target
completions. It is implied by inclusion of K(H) in an ambient class
whose members are ordinarily irreducible. -/
def GenuinePartite2019CanonicalIrreducible
    (H : GenuinePartite2019Class (L := L) (Parts := Parts)) : Prop :=
  ∀ {X : Type w}
    (D : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
    canonicalGenuineTagged2019Class H D → D.Irreducible

/-- The ambient inclusion and irreducibility assumptions of the
already verified functional Ramsey endpoint automatically supply
irreducibility of each canonical H target. -/
theorem genuinePartite2019_canonicalIrreducible_of_ambient
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (R : StructureClass
      (L := (L.withParts Parts).wholeMaskTagLanguage Parts))
    (hRIrred : ∀ {X : Type w}
      (D : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      R D → D.Irreducible)
    (hSub : ∀ {X : Type w}
      (D : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H D → R D) :
    GenuinePartite2019CanonicalIrreducible H := by
  intro X D hK
  exact hRIrred D (hSub D hK)

/-- More general CLOSED base: every U-closed and U-irreducible
induced test of a corrected-(4b)-covered candidate C ALREADY
belongs to the canonical class K(H), and therefore completes via
the identity map when canonical H-targets are ordinary irreducibles.
No generator-rank bound is necessary at this stage. -/
theorem genuineTagged2019_closedUIrreducible_relativeCompletion
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hKIrred : GenuinePartite2019CanonicalIrreducible H)
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (T : Set V) [Fintype T]
    (hTClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T))
    (hTIrred :
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T)) :
    HasGenuinePartiteTagged2019RelativeCompletion H
      (C.induce T) := by
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  have hTK : canonicalGenuineTagged2019Class H (C.induce T) :=
    hCovered T hTClosed hTIrred
  have hOrdIrred : (C.induce T).Irreducible :=
    hKIrred (C.induce T) hTK
  let e : RelStructure.Embedding (C.induce T) (C.induce T) :=
    RelStructure.Embedding.id (C.induce T)
  have he : IsInducedClosedUHomomorphismEmbedding
      rules (C.induce T) (C.induce T) e.toFun :=
    IsClosedUHomomorphismEmbedding.toInducedClosed
      (e.isClosedUHomomorphismEmbedding rules)
  exact (canonicalGenuineTagged2019_KCompletion_iff_relative
    H (C.induce T)).mp
      ⟨T, inferInstance, C.induce T, hTK, hOrdIrred, e.toFun, he⟩

/-- Rank-one CLOSED base. A corrected (4b) candidate's U-closed
induced T with USize <=1 is itself a canonical H-member, because
it is U-irreducible. It therefore has a genuine H-relative
completion by the IDENTITY map. No enlargement of T or independent
local-completion assumption is used. -/
theorem genuineTagged2019_closedRankOne_relativeCompletion
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hKIrred : GenuinePartite2019CanonicalIrreducible H)
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (T : Set V) [Fintype T]
    (hTClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T))
    (hRank :
      USize ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) ≤ 1) :
    HasGenuinePartiteTagged2019RelativeCompletion H
      (C.induce T) := by
  have hTIrred : IsUIrreducible
      ((L.withParts Parts).wholeMaskClosureRules Parts) (C.induce T) :=
    hTClosed.uIrreducible_of_USize_le_one hRank
  exact genuineTagged2019_closedUIrreducible_relativeCompletion
    H hKIrred C hCovered T hTClosed hTIrred

/-- Every ORDINARY irreducible exact weak OLD induced support
has an H-relative completion already under corrected (4b), provided
all canonical H members are ordinary irreducibles. This uses the
full canonical embedding of the unchanged induced support into
some genuine H target. No rank or closure assumption on S occurs. -/
theorem genuineTagged2019_irreducibleWeak_relativeCompletion
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hKIrred : GenuinePartite2019CanonicalIrreducible H)
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (S : Set V) (hSIrred : (C.induce S).Irreducible) :
    HasGenuinePartiteTagged2019RelativeCompletion H
      (C.induce S) := by
  classical
  obtain ⟨X, hFinite, Target, targetPart, hH, hTr, ⟨e⟩⟩ :=
    genuineTagged2019_correctedCovered_weakIrred_canonicalTarget
      H C hClosed hCovered S hSIrred
  letI : Finite X := hFinite
  let D := wholeMaskTagExpansion (withPartsWholeMaskOld Target targetPart)
  have hK : canonicalGenuineTagged2019Class H D :=
    canonicalGenuineTagged2019Class_mem H Target targetPart hH hTr
  have hIrred : D.Irreducible := hKIrred D hK
  have he : IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce S) D e.toFun :=
    IsClosedUHomomorphismEmbedding.toInducedClosed
      (e.isClosedUHomomorphismEmbedding
        ((L.withParts Parts).wholeMaskClosureRules Parts))
  exact ⟨X, hFinite, Target, targetPart, hH, hTr, hIrred,
    e.toFun, he⟩

/-- Stronger EXACT WEAK singleton base. Corrected (4b) and
U-closedness of the ambient C, plus irreducibility of canonical
H-members, force genuine H-relative completions of all
OLD induced tests with at most one vertex.

The test itself need not be function-closed. Its persistent OLD
domain masks are fully preserved because the witness is a FULL
relational embedding into a canonical genuinely partial H-target.
The cutoff one is unchanged, including the empty test. -/
theorem genuineTagged2019_allWeakAtOne_relativeCompletion
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hKIrred : GenuinePartite2019CanonicalIrreducible H)
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (S : Finset V) (hSize : S.card ≤ 1) :
    HasGenuinePartiteTagged2019RelativeCompletion H
      (C.induce (↑S : Set V)) := by
  classical
  let SS : Set V := (↑S : Set V)
  have hSingletonIrred : (C.induce SS).Irreducible := by
    intro x y hxy
    apply hxy
    apply Subtype.ext
    exact Finset.card_le_one.mp hSize x.1 x.2 y.1 y.2
  exact genuineTagged2019_irreducibleWeak_relativeCompletion
    H hKIrred C hClosed hCovered SS hSingletonIrred

/-- Hence the cutoff-one all-weak-test premise of the corrected
2019 local-completion axiom is AUTOMATIC from (4b) when canonical
K(H) is irreducible. Unlike the naive FULL intrinsic-weak test
premise, this is not the fixed-point-free unary vacuity argument:
the map protects persistent OLD domain records. -/
theorem genuineTagged2019_localAtOne_copywise_of_covered
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hKIrred : GenuinePartite2019CanonicalIrreducible H)
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) W)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (hLocal : GenuinePartiteTagged2019LocalCompletionAt H B C0 1)
    {X : Type w} [Finite X]
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hControl : C0.Irreducible ∧ ∃ p : X → Z,
      IsInducedClosedUHomomorphismEmbedding
        ((L.withParts Parts).wholeMaskClosureRules Parts) C C0 p)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C) :
    HasCopywiseCompletion (canonicalGenuineTagged2019Class H) B C := by
  apply hLocal C hClosed hControl hCovered
  intro S hSize
  exact genuineTagged2019_allWeakAtOne_relativeCompletion
    H hKIrred C hClosed hCovered S hSize

end AllThoseRamseyClasses.Published
