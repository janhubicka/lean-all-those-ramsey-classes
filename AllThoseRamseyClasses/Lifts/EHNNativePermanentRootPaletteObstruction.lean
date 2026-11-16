import AllThoseRamseyClasses.Lifts.EHNPrintedTupleImageClosure
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Track D: native full-amalgamation obstruction to finite root palettes

A central assertion in the 16 November 2026 Track D counterexample
audit is that a single finite closed original root can have
arbitrarily many pairwise PERMANENTLY incompatible finite original
extensions. A precompact hereditary AP lift with exact old shadows
would have to give distinct expanded root types to these extensions.

This module formalizes the GENERAL NECESSARY COMBINATORIAL STEP
against the actual native FULL-embedding amalgamation predicate,
with an explicit target-old allowed class. It does not assume a
free amalgam, a common maximal canonical lift, root injection by
a weak EHN map, or bounded forbidden-source size.

If any two allowed rooted old extensions assigned the same finite
root code admit an allowed full-native amalgam over their original
root, then pairwise NONAMALGAMABLE extensions must all receive
different codes. In particular, n such extensions need at least n
root codes. If these families exist at every finite size, NO finite
root palette can have this amalgamation guarantee.

This is the exact finite-pigeonhole interface for a future
native Lean formalization of the concrete Boolean contexts in
the antichain example. It is NOT a native certificate for the
infinite counterexample itself, nor a theorem that a particular
unrestricted lift has the assumed code-amalgamation property.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An ACTUAL old-language FULL amalgam of two full rooted
extensions in a specified allowed class, allowing arbitrary
cross tuples and additional vertices. The two ambient
embeddings agree on EVERY vertex of the genuine old root.

No assumption of free amalgamation, disjointness outside
the root, or functional closure of a weak image is made. -/
def HasAllowedNativeFullAmalgamOver
    (Allowed : ∀ {X : Type}, Structure L X → Prop)
    {RX VA VB : Type}
    (Root : Structure L RX)
    (A : Structure L VA) (B : Structure L VB)
    (iA : Structure.Embedding Root A)
    (iB : Structure.Embedding Root B) : Prop :=
  ∃ (Z : Type) (D : Structure L Z),
    Allowed D ∧
    ∃ (jA : Structure.Embedding A D)
      (jB : Structure.Embedding B D),
      ∀ r : RX, jA (iA r) = jB (iB r)

/-- Two ROOTED old extensions of the same original old root
which cannot be jointly fully embedded over that root into
ANY structure of the given allowed old class.

This is a stronger semantic assertion than the failure of
their FREE amalgam to be allowed. -/
def PermanentlyIncompatibleNativeRootExtensions
    (Allowed : ∀ {X : Type}, Structure L X → Prop)
    {RX VA VB : Type}
    (Root : Structure L RX)
    (A : Structure L VA) (B : Structure L VB)
    (iA : Structure.Embedding Root A)
    (iB : Structure.Embedding Root B) : Prop :=
  ¬ HasAllowedNativeFullAmalgamOver Allowed Root A B iA iB

/-- A family of ACTUAL genuine full native rooted extensions
is pairwise permanently incompatible if every distinct pair
has NO allowed full amalgam over the original root. -/
def PairwiseIncompatibleNativeRootFamily
    (Allowed : ∀ {X : Type}, Structure L X → Prop)
    {RX I : Type}
    (Root : Structure L RX)
    {V : I → Type}
    (A : ∀ i : I, Structure L (V i))
    (root : ∀ i : I, Structure.Embedding Root (A i)) : Prop :=
  ∀ i j : I, i ≠ j →
    PermanentlyIncompatibleNativeRootExtensions
      Allowed Root (A i) (A j) (root i) (root j)

/-- A root-code assignment which guarantees an allowed native
FULL amalgam whenever two rooted old extensions receive the
same root code. This is the exact necessary AP implication
from a hereditary exact-shadow lift when equality of finite
root expansion types entails amalgamation.

A root-code assignment alone is not called a lift; the
amalgamation guarantee is a separate EXPLICIT hypothesis. -/
def RootCodesForceAllowedAmalgamation
    (Allowed : ∀ {X : Type}, Structure L X → Prop)
    {RX I C : Type}
    (Root : Structure L RX)
    {V : I → Type}
    (A : ∀ i : I, Structure L (V i))
    (root : ∀ i : I, Structure.Embedding Root (A i))
    (code : I → C) : Prop :=
  ∀ i j : I, code i = code j →
    HasAllowedNativeFullAmalgamOver
      Allowed Root (A i) (A j) (root i) (root j)

/-- DISTINCT original rooted extensions with no permitted
full amalgam must carry DISTINCT root codes whenever equal
codes guarantee an allowed full amalgam.

This is an ACTUAL native-structure proof, not merely a graph
or abstract-colouring substitution for amalgamation. -/
theorem pairwiseIncompatible_rootCodes_injective
    (Allowed : ∀ {X : Type}, Structure L X → Prop)
    {RX I C : Type}
    (Root : Structure L RX)
    {V : I → Type}
    (A : ∀ i : I, Structure L (V i))
    (root : ∀ i : I, Structure.Embedding Root (A i))
    (code : I → C)
    (hPairwise :
      PairwiseIncompatibleNativeRootFamily Allowed Root A root)
    (hCodes :
      RootCodesForceAllowedAmalgamation Allowed Root A root code) :
    Function.Injective code := by
  intro i j hij
  by_contra hDistinct
  exact (hPairwise i j hDistinct) (hCodes i j hij)

/-- Finite root-colour lower bound for a native family of
pairwise permanently incompatible old extensions.
The number of colours must be at least the number of old
extensions, not merely the number of vertices of the root. -/
theorem finiteRootPalette_card_ge_pairwiseNativeIncompatible
    (Allowed : ∀ {X : Type}, Structure L X → Prop)
    {RX I C : Type} [Fintype I] [Fintype C]
    (Root : Structure L RX)
    {V : I → Type}
    (A : ∀ i : I, Structure L (V i))
    (root : ∀ i : I, Structure.Embedding Root (A i))
    (code : I → C)
    (hPairwise :
      PairwiseIncompatibleNativeRootFamily Allowed Root A root)
    (hCodes :
      RootCodesForceAllowedAmalgamation Allowed Root A root code) :
    Fintype.card I ≤ Fintype.card C := by
  exact Fintype.card_le_of_injective code
    (pairwiseIncompatible_rootCodes_injective
      Allowed Root A root code hPairwise hCodes)

/-- FINITE INDEX specialization: if n actual old extensions
of a single old root are pairwise permanently incompatible,
no finite palette of fewer than n root codes can have the
full-amalgamation guarantee for all those extensions. -/
theorem finiteRootPalette_card_ge_Fin_nativeIncompatible
    (Allowed : ∀ {X : Type}, Structure L X → Prop)
    {RX C : Type} [Fintype C]
    (Root : Structure L RX)
    {n : ℕ}
    {V : Fin n → Type}
    (A : ∀ i : Fin n, Structure L (V i))
    (root : ∀ i : Fin n, Structure.Embedding Root (A i))
    (code : Fin n → C)
    (hPairwise :
      PairwiseIncompatibleNativeRootFamily Allowed Root A root)
    (hCodes :
      RootCodesForceAllowedAmalgamation Allowed Root A root code) :
    n ≤ Fintype.card C := by
  simpa only [Fintype.card_fin] using
    (finiteRootPalette_card_ge_pairwiseNativeIncompatible
      Allowed Root A root code hPairwise hCodes)

/-- There are arbitrarily large FINITE families of allowed
old-source full embeddings of one fixed original native root
that cannot be pairwise amalgamated in the old allowed class.
The carriers may depend on the index, and no uniform carrier
bound or fixed target is assumed. -/
def ArbitrarilyManyPermanentlyIncompatibleNativeRootExtensions
    (Allowed : ∀ {X : Type}, Structure L X → Prop)
    {RX : Type} (Root : Structure L RX) : Prop :=
  ∀ n : ℕ,
    ∃ (V : Fin n → Type)
      (A : ∀ i : Fin n, Structure L (V i))
      (root : ∀ i : Fin n, Structure.Embedding Root (A i)),
      (∀ i : Fin n, Allowed (A i)) ∧
      PairwiseIncompatibleNativeRootFamily Allowed Root A root

/-- A finite root palette supports EVERY finite family of
allowed old rooted extensions if it can assign codes with
the property that equal codes imply an allowed full native
amalgam over the original root.

This is exactly the consequence of hereditary exact reduct
and amalgamation plus a finite fibre over the old root;
we leave the passage from any concrete expansion API to
this condition as an independent validation obligation. -/
def FiniteRootPaletteSupportsNativeAmalgamation
    (Allowed : ∀ {X : Type}, Structure L X → Prop)
    {RX C : Type}
    (Root : Structure L RX) : Prop :=
  ∀ n : ℕ,
    ∀ (V : Fin n → Type)
      (A : ∀ i : Fin n, Structure L (V i))
      (root : ∀ i : Fin n, Structure.Embedding Root (A i)),
      (∀ i : Fin n, Allowed (A i)) →
      ∃ code : Fin n → C,
        RootCodesForceAllowedAmalgamation
          Allowed Root A root code

/-- UNBOUNDED native permanent incompatibility at ONE fixed
old root RULES OUT any finite root-code palette satisfying
the exact amalgamation implication for all allowed finite
root extensions.

This holds for arbitrary native languages including genuine
partial set-valued functions; it assumes no source-size bound,
precompactness of the original lift, or weak-image quotient.
The concrete anti-chain context family from the Track D
English audit is the remaining missing input, not secretly
assumed in this abstract implication. -/
theorem noFiniteRootPalette_of_arbitrarilyNativeIncompatible
    (Allowed : ∀ {X : Type}, Structure L X → Prop)
    {RX C : Type} [Fintype C]
    (Root : Structure L RX)
    (hIncompatible :
      ArbitrarilyManyPermanentlyIncompatibleNativeRootExtensions
        Allowed Root) :
    ¬ FiniteRootPaletteSupportsNativeAmalgamation
        Allowed (C := C) Root := by
  intro hPalette
  let n : ℕ := Fintype.card C + 1
  obtain ⟨V, A, root, hAllowed, hPairwise⟩ :=
    hIncompatible n
  obtain ⟨code, hCodes⟩ :=
    hPalette n V A root hAllowed
  have hBound : n ≤ Fintype.card C :=
    finiteRootPalette_card_ge_Fin_nativeIncompatible
      Allowed Root A root code hPairwise hCodes
  dsimp [n] at hBound
  omega

end AllThoseRamseyClasses.Lifts
