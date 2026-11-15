import AllThoseRamseyClasses.Lifts.Claim2NeutralQFullSeamFactor
import AllThoseRamseyClasses.Lifts.Claim2SelectedQAactiveSourceCost

/-!
# Structural obstruction to preserving global A-source minimality in Claim 2

A genuinely selected replacement Q which contributes no B-exclusive
vertices can be A-neutral ONLY if its full weak EHN image factors
into the full shared root X, with exact target coordinates.

Consequently, if there exists NO EHN map Q -> X, the ACTUAL
replacement necessarily creates an A-exclusive private Q-nonroot
SOURCE vertex. By the verified exact selected-Q source-cost law,
replacing an old A-free component strictly INCREASES the number
of A-exclusive SOURCE vertices of the forbidden witness.

This gives a concrete structural obstruction to preserving the
original global A-support minimizer across B-to-A flips.
It does not assert that the necessary no-EHN premise holds for
all rooted forbidden selected pieces; establishing or disproving
such a premise is part of the remaining original-2019 proof.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- If a B-inactive rooted genuine Q with seam-valued complete root
cannot admit ANY EHN homomorphism-embedding into the full common
target root X, then it MUST contain a private nonroot SOURCE vertex
mapped to the A-exclusive target part.

The exact NEW Q target map and actual source embedding are retained;
no source map is assumed injective and no image quotient is formed. -/
theorem fullNativeRootedPiece_noEHNinX_forces_privateA
    {Q W UX UA UB UT : Type}
    (Piece : Structure L Q) (New : Structure L W)
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (iQ : Structure.Embedding Piece New)
    (flip : W → UT)
    (hFlip : New.IsEHNHomomorphismEmbedding Target flip)
    {m : ℕ} (roots : Fin m → Q)
    (hRootSeam : ∀ i : Fin m,
      flip (iQ (roots i)) ∈ Set.range (jLeft.comp iLeft))
    (hNoBFromQ : ∀ q : Q,
      flip (iQ q) ∉ fullFreeRightExclusiveTarget iRight jRight)
    (hNoEHNintoX : ∀ p : Q → UX,
      ¬ Piece.IsEHNHomomorphismEmbedding X p) :
    ∃ q : Q,
      q ∉ Set.range roots ∧
      flip (iQ q) ∈ fullFreeLeftExclusiveTarget iLeft jLeft := by
  classical
  by_contra hNoPrivateA
  have hNeutral : ∀ q : Q,
      q ∉ Set.range roots →
      flip (iQ q) ∉ fullFreeLeftExclusiveTarget iLeft jLeft := by
    intro q hPrivate hA
    exact hNoPrivateA ⟨q, hPrivate, hA⟩
  obtain ⟨p, hp, _hSame⟩ :=
    (fullNativeRootedPiece_Aneutral_iff_exactEHNFullRootFactor
      Piece New Target Left Right X
      iLeft iRight jLeft jRight hFree iQ flip hFlip
      roots hRootSeam hNoBFromQ).mp hNeutral
  exact hNoEHNintoX p hp

/-- If the exact selected-Q native replacement of an A-free old
component has NO new B-exclusive Q vertex but Q cannot weakly
EHN-map into the full common target root, then the TOTAL
A-exclusive SOURCE-vertex count STRICTLY INCREASES.

This uses the exact TRUE finite source-cardinality formula:
new A-count = old A-count + new PRIVATE Q A-count. The
new private A-count is strictly positive by the previous
SOURCE factor obstruction. No global A-minimality hypothesis
is needed: strict increase holds for any such actual flip. -/
theorem geometricSelectedQ_noEHNintoX_strict_AactiveSourceGrowth
    {V W UX UA UB UT : Type}
    (Old : Structure L V)
    {m : ℕ}
    (inner : GeometricFunctionalPieceData Old m)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (New : Structure L W) (hFiniteNew : Finite W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (f : V → UT) (flip : W → UT)
    (hFlip : New.IsEHNHomomorphismEmbedding Target flip)
    (hOldInnerNoA : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left →
      f z ∉ fullFreeLeftExclusiveTarget iLeft jLeft)
    (hEAgree :
      ∀ e : (geometricGlobalComplementChart Old inner).Carrier,
        flip (iE e) = f e.1)
    (hQRootSeam : ∀ i : Fin m,
      flip (iQ (Q.rootEmbedding i)) ∈ Set.range (jLeft.comp iLeft))
    (hNoBFromQ : ∀ q : Q.Carrier,
      flip (iQ q) ∉ fullFreeRightExclusiveTarget iRight jRight)
    (hNoEHNintoX : ∀ p : Q.Carrier → UX,
      ¬ Q.str.IsEHNHomomorphismEmbedding X p) :
    Nat.card {v : V //
      f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} <
    Nat.card {w : W //
      flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
  classical
  obtain ⟨q, hPrivate, hA⟩ :=
    fullNativeRootedPiece_noEHNinX_forces_privateA
      Q.str New Target Left Right X
      iLeft iRight jLeft jRight hFree iQ flip hFlip
      Q.rootEmbedding hQRootSeam hNoBFromQ hNoEHNintoX
  letI : Finite Q.Carrier :=
    Finite.of_injective (fun q : Q.Carrier => iQ q) iQ.injective
  letI : Fintype Q.Carrier := Fintype.ofFinite Q.Carrier
  have hPrivateNonempty :
      Nonempty {q : Q.Carrier //
        q ∉ Set.range Q.rootEmbedding ∧
        flip (iQ q) ∈ fullFreeLeftExclusiveTarget iLeft jLeft} :=
    ⟨⟨q, hPrivate, hA⟩⟩
  have hPrivatePositive :
      0 < Nat.card {q : Q.Carrier //
        q ∉ Set.range Q.rootEmbedding ∧
        flip (iQ q) ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr hPrivateNonempty
  have hCost :
      Nat.card {w : W //
        flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} +
      Nat.card {q : Q.Carrier //
        q ∉ Set.range Q.rootEmbedding ∧
        flip (iQ q) ∈ fullFreeLeftExclusiveTarget iLeft jLeft} :=
    geometricSelectedQ_AfreeOld_exact_Aactive_cost
      Old inner Q New hFiniteNew iQ iE hNewFree
      f flip (fullFreeLeftExclusiveTarget iLeft jLeft)
      hOldInnerNoA hEAgree
  rw [hCost]
  exact Nat.lt_add_of_pos_right hPrivatePositive

end AllThoseRamseyClasses.Lifts
