import AllThoseRamseyClasses.Lifts.GlobalCommonLiftAgreement

/-!
# Maximal canonical piece lifts along a fully embedded substructure

This isolates the formal, easy half of the maximal-witness assertion
in the proof of `lem:amalgamationstr` of the 2019 paper.

Fix a class K of allowed full functional structures, intended later
to be `Forb(F)`. A global canonical lift of A is "maximal along"
an embedding X -> A when EVERY full extension A -> C with C in K
induces EXACTLY the same added piece-class relations on the
designated common carrier X. The old relation and function tables
are already preserved by the full embeddings.

The main lemma proves stability of this maximality under further
K-extensions: if A is maximal along X and an extension D is in K,
then D is maximal along the same copy of X.

An additional lemma shows that maximal witnesses A and B whose
copies of X agree INSIDE a common K-extension D necessarily have
identical global added relations on X. This is the precise bridge
used once the hard combinatorial proof has established D in Forb(F).

We do NOT assume that the free amalgam of A and B belongs to K.
That is the substantive content of the later flip/minimal-piece
strong-amalgamation argument. Nor do we derive K-membership from
maximality itself.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The canonical F-lift of A is maximal along the specific full
embedding of X if every allowed extension of A leaves all global
piece-class predicates on the image of X unchanged.

K is supplied as a class predicate. Taking K = Forb(F) recovers
the paper's original maximality notion, up to transporting literal
substructures by full embeddings. -/
def GlobalCanonicalMaximalAlong
    (F K : ∀ {W : Type}, Structure L W → Prop)
    {UX UA : Type}
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A) : Prop :=
  ∀ {UC : Type} (C : Structure L UC), K C →
    (e : Structure.Embedding A C) →
    ∀ (s : GlobalFunctionalPieceSymbol F)
      (xs : Fin (globalFunctionalPieceArity F s) → UX),
      (globalFunctionalCanonicalLift F C).rel (.inr s)
        (e ∘ iA ∘ xs) ↔
      (globalFunctionalCanonicalLift F A).rel (.inr s)
        (iA ∘ xs)

/-- Every allowed full extension of a maximal lift induces the
SAME canonical global piece relations on the prescribed copy of X.
This is the direct, source-matched unpacking of maximality. -/
theorem GlobalCanonicalMaximalAlong.relation_extension
    (F K : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UC : Type}
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A)
    (hmax : GlobalCanonicalMaximalAlong F K iA)
    (C : Structure L UC) (hC : K C)
    (e : Structure.Embedding A C)
    (s : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F s) → UX) :
    (globalFunctionalCanonicalLift F C).rel (.inr s)
      (e ∘ iA ∘ xs) ↔
    (globalFunctionalCanonicalLift F A).rel (.inr s)
      (iA ∘ xs) :=
  hmax C hC e s xs

/-- If A is maximal along X, any allowed full extension D is ALSO
maximal along its copy of X, since every subsequent extension
of D is already an extension of A.

This is the "D is still a witness once D is forbidden-free"
part of the printed strong-amalgamation proof. -/
theorem GlobalCanonicalMaximalAlong.of_allowed_extension
    (F K : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UD : Type}
    {X : Structure L UX}
    {A : Structure L UA} {D : Structure L UD}
    (iA : Structure.Embedding X A)
    (hmax : GlobalCanonicalMaximalAlong F K iA)
    (hD : K D)
    (eAD : Structure.Embedding A D) :
    GlobalCanonicalMaximalAlong F K (eAD.comp iA) := by
  intro UC C hC eDC s xs
  have hCfromA := hmax C hC (eDC.comp eAD) s xs
  have hDfromA := hmax D hD eAD s xs
  simpa only [Function.comp_assoc] using
    hCfromA.trans hDfromA.symm

/-- Two maximal canonical lift witnesses have the same new
relations on their common embedded substructure whenever a
single allowed structure D contains both copies compatibly.

The hypothesis that D is allowed is explicit. In the 2019
application establishing this hypothesis for the free amalgam
is precisely the nontrivial flip/minimal-subpiece argument. -/
theorem maximalLifts_agree_in_allowed_common_extension
    (F K : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB UD : Type}
    {X : Structure L UX} {A : Structure L UA}
    {B : Structure L UB} {D : Structure L UD}
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B)
    (hMaxA : GlobalCanonicalMaximalAlong F K iA)
    (hMaxB : GlobalCanonicalMaximalAlong F K iB)
    (hD : K D)
    (eA : Structure.Embedding A D)
    (eB : Structure.Embedding B D)
    (hCommon : ∀ x : UX, eA (iA x) = eB (iB x)) :
    GlobalCanonicalLiftsAgreeOn F iA iB := by
  intro s xs
  have hA := hMaxA D hD eA s xs
  have hB := hMaxB D hD eB s xs
  have hTuple :
      (eA ∘ iA ∘ xs) = (eB ∘ iB ∘ xs) := by
    funext j
    exact hCommon (xs j)
  calc
    (globalFunctionalCanonicalLift F A).rel (.inr s) (iA ∘ xs) ↔
      (globalFunctionalCanonicalLift F D).rel (.inr s)
        (eA ∘ iA ∘ xs) := hA.symm
    _ ↔ (globalFunctionalCanonicalLift F D).rel (.inr s)
        (eB ∘ iB ∘ xs) := by rw [hTuple]
    _ ↔ (globalFunctionalCanonicalLift F B).rel (.inr s)
        (iB ∘ xs) := hB

end AllThoseRamseyClasses.Lifts
