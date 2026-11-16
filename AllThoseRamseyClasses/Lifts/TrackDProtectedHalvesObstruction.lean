import AllThoseRamseyClasses.Lifts.ArbitraryFunctionalFreeFold
import AllThoseRamseyClasses.Lifts.GlobalForbiddenEHNAvoidance
import Mathlib.Data.Fintype.Card

/-!
# Track D: protected EHN halves forbid every rooted amalgam

This is the general structural kernel of the proposed actual
counterexample to the printed unrestricted lift theorem. It does
NOT assume a free target amalgam, distinct source-root images,
tuple-surjectivity, a finite forbidden family, absence of native
functions, or finite source-size bounds beyond finiteness of the
one actual forbidden source.

Suppose an original forbidden source S is an ACTUAL full native
free amalgam of P and Q over a closed R. Suppose P and Q each have
EHN maps into left and right target halves, with their source-root
values agreeing through one (possibly noninjective) map R -> X.
Then there is NO original-forbidden-free target containing full
copies of those halves identified over X, even if that target
adds arbitrary positive cross tuples or extra vertices.

The proof composes the two EHN maps with the FULL target-side
embeddings and invokes the already established arbitrary-source
functional EHN fold theorem. Every full irreducible source test
lies in a protected half. This is the decisive arbitrary-amalgam
obstruction and is independent of any source quotient.

A second lemma records the purely logical finite-fibre lower bound:
pairwise nonamalgamable old rooted contexts must have distinct
lifted root profiles in ANY proposed AP expansion. This is an
explicit conditional interface, NOT a fabricated lift AP proof.

The concrete cyclic Gamma_m and decorated ternary half tables
must still be instantiated as genuine native Structure values.
No such instance is claimed proved here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u

variable {L : Language.{u}}

/-- Any common-root amalgam of two full sides INSIDE the
original EHN-forbidden-free class. The new ambient target may
contain arbitrary cross relations and new vertices. -/
def HasAllowedRootedAmalgam
    (F : ∀ {W : Type}, Structure L W → Prop)
    {VX VA VB : Type}
    (X : Structure L VX)
    (A : Structure L VA) (B : Structure L VB)
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B) : Prop :=
  ∃ (W : Type) (D : Structure L W),
    AvoidsGlobalFunctionalEHN F D ∧
    ∃ (jA : Structure.Embedding A D)
      (jB : Structure.Embedding B D),
      ∀ x : VX, jA (iA x) = jB (iB x)

/-- Actual EHN-realizable halves of the SAME forbidden original
source are permanently incompatible over a shared FULL old root.

The map rootToX need not be injective. Both original source halves
embed fully into the forbidden S, and their common native closed-root
diagram genuinely presents S as a free amalgam. The target D, if it
existed, need NOT be their free amalgam: the side copies being FULL
is precisely why arbitrary cross tuples do not affect their EHN maps.
-/
theorem noAllowedRootedAmalgam_of_protectedForbiddenHalves
    (F : ∀ {W : Type}, Structure L W → Prop)
    {VR VP VQ VS VX VA VB : Type}
    (Root : Structure L VR)
    (PieceA : Structure L VP)
    (PieceB : Structure L VQ)
    (Source : Structure L VS)
    (hFinite : Finite VS) (hForbidden : F Source)
    (sA : Structure.Embedding Root PieceA)
    (sB : Structure.Embedding Root PieceB)
    (uA : Structure.Embedding PieceA Source)
    (uB : Structure.Embedding PieceB Source)
    (hSourceFree : Structure.IsFreeAmalgam sA sB uA uB)
    (X : Structure L VX)
    (Left : Structure L VA)
    (Right : Structure L VB)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (pA : VP → VA) (pB : VQ → VB)
    (hpA : PieceA.IsEHNHomomorphismEmbedding Left pA)
    (hpB : PieceB.IsEHNHomomorphismEmbedding Right pB)
    (rootToX : VR → VX)
    (hpARoot : ∀ r : VR, pA (sA r) = iLeft (rootToX r))
    (hpBRoot : ∀ r : VR, pB (sB r) = iRight (rootToX r)) :
    ¬ HasAllowedRootedAmalgam F X Left Right iLeft iRight := by
  intro hAmalgam
  obtain ⟨W, D, hAvoid, jLeft, jRight, hMeet⟩ := hAmalgam
  let fA : VP → W := jLeft ∘ pA
  let fB : VQ → W := jRight ∘ pB
  have hCompat : ∀ r : VR, fA (sA r) = fB (sB r) := by
    intro r
    change jLeft (pA (sA r)) = jRight (pB (sB r))
    calc
      jLeft (pA (sA r)) = jLeft (iLeft (rootToX r)) :=
        congrArg jLeft (hpARoot r)
      _ = jRight (iRight (rootToX r)) := hMeet (rootToX r)
      _ = jRight (pB (sB r)) :=
        congrArg jRight (hpBRoot r).symm
  have hA :
      PieceA.IsEHNHomomorphismEmbedding D fA :=
    jLeft.isEHNHomomorphismEmbedding.comp hpA
  have hB :
      PieceB.IsEHNHomomorphismEmbedding D fB :=
    jRight.isEHNHomomorphismEmbedding.comp hpB
  have hFold :
      Source.IsEHNHomomorphismEmbedding D
        (compatibleFunctionalFold hSourceFree fA fB hCompat) :=
    compatibleFunctionalFold_isEHNHomomorphismEmbedding
      hSourceFree fA fB hCompat hA hB
  exact (hAvoid Source hFinite hForbidden
    (compatibleFunctionalFold hSourceFree fA fB hCompat)) hFold

/-- Every family of genuinely pairwise rooted NONAMALGAMABLE
old contexts requires distinct root profiles in any candidate
AP expansion whose equal root profiles imply an old amalgam. -/
theorem injectiveRootProfiles_of_pairwiseNonamalgamable
    (F : ∀ {W : Type}, Structure L W → Prop)
    {I Profile VX VA : Type}
    (X : Structure L VX)
    (A : I → Structure L VA)
    (iA : ∀ i : I, Structure.Embedding X (A i))
    (profile : I → Profile)
    (hNoAmalgam : ∀ i j : I, i ≠ j →
      ¬ HasAllowedRootedAmalgam F X (A i) (A j) (iA i) (iA j))
    (hSameProfileAmalgam : ∀ i j : I,
      profile i = profile j →
      HasAllowedRootedAmalgam F X (A i) (A j) (iA i) (iA j)) :
    Function.Injective profile := by
  intro i j hSame
  by_contra hDifferent
  exact (hNoAmalgam i j hDifferent)
    (hSameProfileAmalgam i j hSame)

/-- The exact 2^r root-type lower bound underlying the alleged
precompactness obstruction, once the concrete 2^r incompatible
original contexts and the candidate expansion's rooted-AP
reflection have been supplied. -/
theorem twoPow_le_card_rootProfiles_of_nonamalgamable
    (F : ∀ {W : Type}, Structure L W → Prop)
    (r : ℕ)
    {Profile VX VA : Type}
    [Fintype Profile]
    (X : Structure L VX)
    (A : Fin (2 ^ r) → Structure L VA)
    (iA : ∀ i : Fin (2 ^ r), Structure.Embedding X (A i))
    (profile : Fin (2 ^ r) → Profile)
    (hNoAmalgam : ∀ i j : Fin (2 ^ r), i ≠ j →
      ¬ HasAllowedRootedAmalgam F X (A i) (A j) (iA i) (iA j))
    (hSameProfileAmalgam : ∀ i j : Fin (2 ^ r),
      profile i = profile j →
      HasAllowedRootedAmalgam F X (A i) (A j) (iA i) (iA j)) :
    2 ^ r ≤ Fintype.card Profile := by
  have hinj : Function.Injective profile :=
    injectiveRootProfiles_of_pairwiseNonamalgamable
      F X A iA profile hNoAmalgam hSameProfileAmalgam
  simpa using (Fintype.card_le_of_injective profile hinj)

end AllThoseRamseyClasses.Lifts
