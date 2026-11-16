import AllThoseRamseyClasses.Lifts.EHNProtectedSourceFreeAmalgamGluing
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Track D: Boolean families of permanently incompatible rooted contexts

The 16 November 2026 antichain counterexample constructs, for
each finite index i, two allowed native rooted halves L_i and
R_i which are PERMANENTLY incompatible over a fixed full old
root. For every Boolean word eta on r indices, its context
C_eta contains a FULL rooted copy of the chosen half at every
index. This module isolates the exact native semantical
consequence:

  eta ≠ theta ⇒ C_eta and C_theta have NO allowed full amalgam
  over their original root.

The proof chooses a differing index, restricts a hypothetical
FULL amalgam of the contexts to the two FULL selected rooted
halves, and contradicts their permanent incompatibility.
Arbitrary cross-tuple completion and additional target vertices
are allowed inside the alleged full amalgam.

Consequently 2^r such Boolean contexts force at least 2^r
distinct root codes in ANY palette where equal root codes
guarantee an allowed full native amalgam.

No infinite decorated Gamma_m source or context construction
is asserted to exist here: the existence, membership in the
allowed old shadow class and root embeddings are transparent
hypotheses. This is a rigorously scoped native combinatorial
handoff for formalizing the explicit counterexample.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A genuine allowed full rooted amalgam of B and A can be
swapped to give an allowed full rooted amalgam of A and B.
No free amalgam or disjointness assumption. -/
theorem nativeAllowedFullAmalgam_symm
    (Allowed : ∀ {X : Type}, Structure L X → Prop)
    {RX VA VB : Type}
    (Root : Structure L RX)
    (A : Structure L VA) (B : Structure L VB)
    (iA : Structure.Embedding Root A)
    (iB : Structure.Embedding Root B)
    (h : HasAllowedNativeFullAmalgamOver
      Allowed Root B A iB iA) :
    HasAllowedNativeFullAmalgamOver
      Allowed Root A B iA iB := by
  obtain ⟨W, D, hAllowed, eB, eA, hRoot⟩ := h
  exact ⟨W, D, hAllowed, eA, eB,
    fun x => (hRoot x).symm⟩

/-- In a Boolean family of full native rooted contexts,
each context realizes a FULL rooted copy of one of two
alternative old halves at every index.

The alternatives are permanently incompatible, NOT merely
incompatible under FREE amalgamation. Therefore every pair
of distinct Boolean contexts is permanently nonamalgamable
over the SAME original full old root. -/
theorem nativeBooleanContexts_pairwisePermanentlyIncompatible
    (Allowed : ∀ {X : Type}, Structure L X → Prop)
    {RX : Type} (Root : Structure L RX)
    {r : ℕ}
    (VH : Fin r → Bool → Type)
    (Half : ∀ (i : Fin r) (b : Bool),
      Structure L (VH i b))
    (rootHalf : ∀ (i : Fin r) (b : Bool),
      Structure.Embedding Root (Half i b))
    (hOpposite : ∀ i : Fin r,
      PermanentlyIncompatibleNativeRootExtensions
        Allowed Root (Half i false) (Half i true)
        (rootHalf i false) (rootHalf i true))
    (VC : (Fin r → Bool) → Type)
    (Ctx : ∀ eta : Fin r → Bool,
      Structure L (VC eta))
    (rootCtx : ∀ eta : Fin r → Bool,
      Structure.Embedding Root (Ctx eta))
    (embedHalf : ∀ (eta : Fin r → Bool) (i : Fin r),
      Structure.Embedding (Half i (eta i)) (Ctx eta))
    (hEmbedRoot : ∀ (eta : Fin r → Bool) (i : Fin r)
        (z : RX),
      embedHalf eta i (rootHalf i (eta i) z) =
        rootCtx eta z) :
    PairwiseIncompatibleNativeRootFamily
      Allowed Root Ctx rootCtx := by
  classical
  intro eta theta hDistinct
  have hDifference : ∃ i : Fin r, eta i ≠ theta i := by
    by_contra hNone
    have hEqual : eta = theta := by
      funext i
      by_contra hDiff
      exact hNone ⟨i, hDiff⟩
    exact hDistinct hEqual
  obtain ⟨i, hDiff⟩ := hDifference
  intro hAmalgam
  obtain ⟨W, D, hAllowed, jEta, jTheta, hRootAgree⟩ :=
    hAmalgam
  let eLeft : Structure.Embedding (Half i (eta i)) D :=
    jEta.comp (embedHalf eta i)
  let eRight : Structure.Embedding (Half i (theta i)) D :=
    jTheta.comp (embedHalf theta i)
  have hAgree (z : RX) :
      eLeft (rootHalf i (eta i) z) =
        eRight (rootHalf i (theta i) z) := by
    calc
      eLeft (rootHalf i (eta i) z) =
        jEta (rootCtx eta z) :=
          congrArg jEta (hEmbedRoot eta i z)
      _ = jTheta (rootCtx theta z) := hRootAgree z
      _ = eRight (rootHalf i (theta i) z) :=
          congrArg jTheta (hEmbedRoot theta i z).symm
  have hSubAmalgam :
      HasAllowedNativeFullAmalgamOver
        Allowed Root (Half i (eta i)) (Half i (theta i))
        (rootHalf i (eta i)) (rootHalf i (theta i)) :=
    ⟨W, D, hAllowed, eLeft, eRight, hAgree⟩
  cases hEta : eta i <;> cases hTheta : theta i
  · exact hDiff (by rw [hEta, hTheta])
  · exact (hOpposite i)
      (by simpa only [hEta, hTheta] using hSubAmalgam)
  · have hReverse :
        HasAllowedNativeFullAmalgamOver
          Allowed Root (Half i false) (Half i true)
          (rootHalf i false) (rootHalf i true) := by
      apply nativeAllowedFullAmalgam_symm
        Allowed Root (Half i false) (Half i true)
          (rootHalf i false) (rootHalf i true)
      simpa only [hEta, hTheta] using hSubAmalgam
    exact (hOpposite i) hReverse
  · exact hDiff (by rw [hEta, hTheta])

/-- An ACTUAL family indexed by all Boolean r-words, with
permanent incompatibility of opposite full source halves,
forces at least |Bool^(Fin r)| root codes whenever same
root code yields a permitted FULL amalgam of the contexts.

This theorem does not assume the contexts are free amalgams,
only that every chosen half is present FULLY over the root. -/
theorem nativeBooleanContexts_rootPalette_lowerBound
    (Allowed : ∀ {X : Type}, Structure L X → Prop)
    {RX C : Type} [Fintype C]
    (Root : Structure L RX)
    {r : ℕ}
    (VH : Fin r → Bool → Type)
    (Half : ∀ i : Fin r, ∀ b : Bool,
      Structure L (VH i b))
    (rootHalf : ∀ i : Fin r, ∀ b : Bool,
      Structure.Embedding Root (Half i b))
    (hOpposite : ∀ i : Fin r,
      PermanentlyIncompatibleNativeRootExtensions
        Allowed Root (Half i false) (Half i true)
        (rootHalf i false) (rootHalf i true))
    (VC : (Fin r → Bool) → Type)
    (Ctx : ∀ eta : Fin r → Bool,
      Structure L (VC eta))
    (rootCtx : ∀ eta : Fin r → Bool,
      Structure.Embedding Root (Ctx eta))
    (embedHalf : ∀ (eta : Fin r → Bool) (i : Fin r),
      Structure.Embedding (Half i (eta i)) (Ctx eta))
    (hEmbedRoot : ∀ (eta : Fin r → Bool) (i : Fin r)
        (z : RX),
      embedHalf eta i (rootHalf i (eta i) z) =
        rootCtx eta z)
    (code : (Fin r → Bool) → C)
    (hCodes : RootCodesForceAllowedAmalgamation
      Allowed Root Ctx rootCtx code) :
    Fintype.card (Fin r → Bool) ≤ Fintype.card C := by
  let hPairwise :=
    nativeBooleanContexts_pairwisePermanentlyIncompatible
      Allowed Root VH Half rootHalf hOpposite
      VC Ctx rootCtx embedHalf hEmbedRoot
  exact finiteRootPalette_card_ge_pairwiseNativeIncompatible
    Allowed Root Ctx rootCtx code hPairwise hCodes

/-- Explicit EXPONENTIAL bound: Boolean choices at r
independent permanently incompatible rooted half-pairs
require at least 2^r distinct expanded root codes under any
exact-shadow full-amalgamation-compatible palette.

This is a conditional native Lean deduction from TRUE FULL
source embeddings, not merely a finite tabulation of
different Boolean words. -/
theorem nativeBooleanContexts_rootPalette_ge_two_pow
    (Allowed : ∀ {X : Type}, Structure L X → Prop)
    {RX C : Type} [Fintype C]
    (Root : Structure L RX)
    {r : ℕ}
    (VH : Fin r → Bool → Type)
    (Half : ∀ i : Fin r, ∀ b : Bool,
      Structure L (VH i b))
    (rootHalf : ∀ i : Fin r, ∀ b : Bool,
      Structure.Embedding Root (Half i b))
    (hOpposite : ∀ i : Fin r,
      PermanentlyIncompatibleNativeRootExtensions
        Allowed Root (Half i false) (Half i true)
        (rootHalf i false) (rootHalf i true))
    (VC : (Fin r → Bool) → Type)
    (Ctx : ∀ eta : Fin r → Bool,
      Structure L (VC eta))
    (rootCtx : ∀ eta : Fin r → Bool,
      Structure.Embedding Root (Ctx eta))
    (embedHalf : ∀ (eta : Fin r → Bool) (i : Fin r),
      Structure.Embedding (Half i (eta i)) (Ctx eta))
    (hEmbedRoot : ∀ (eta : Fin r → Bool) (i : Fin r)
        (z : RX),
      embedHalf eta i (rootHalf i (eta i) z) =
        rootCtx eta z)
    (code : (Fin r → Bool) → C)
    (hCodes : RootCodesForceAllowedAmalgamation
      Allowed Root Ctx rootCtx code) :
    2 ^ r ≤ Fintype.card C := by
  have hBound :=
    nativeBooleanContexts_rootPalette_lowerBound
      Allowed Root VH Half rootHalf hOpposite
      VC Ctx rootCtx embedHalf hEmbedRoot code hCodes
  simpa only [Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] using hBound

end AllThoseRamseyClasses.Lifts
