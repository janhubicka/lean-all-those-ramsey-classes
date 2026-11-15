import AllThoseRamseyClasses.Lifts.EHNFullSideFactor
import AllThoseRamseyClasses.Lifts.Claim2SelectedOuterActiveBoundaryAnchor

/-!
# A-neutral B-free selected Q factors into the FULL common target root

An actual B-to-A selected-Q replacement has no B-exclusive new
Q image. The exact source-cost proof now says preserving ORIGINAL
global A-source minimality also requires that the newly inserted
Q-nonroot source vertices be A-inactive.

In any ACTUAL full target free amalgam, the three regions
(common seam, A-exclusive, B-exclusive) cover the entire target.
Therefore absence of both exclusive regions, including the
rooted vertices of Q, forces the ENTIRE weak Q image into the
FULL target common root. Restricting the actual EHN weak target
map to the native FULL embedded Q and cancelling the FULL
embedding X -> Target yields an actual EHN weak factorization
of Q into X. This is a NECESSARY structural condition for
A-neutral selected-Q source replacement, not a claim that such
a selected Q exists.

All statements concern original source vertices and exact
full-native source embeddings; the weak target map can be
noninjective. No quotient or target-image cardinality is used.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- In a genuine FULL target free amalgam, a weak target-map
source vertex which is neither A-exclusive nor B-exclusive
necessarily belongs to the exact full shared-root preimage.
No source-map injectivity or EHN hypothesis is needed. -/
theorem weakFree_noExclusive_isSharedRoot
    {U UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (f : U → UT) (x : U)
    (hNotLeft : x ∉ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (hNotRight : x ∉ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f) :
    x ∈ weakFreeRootPart (sL := iLeft) (iL := jLeft) f := by
  rcases weakFreePartition_covers hFree f x with hr | hl | hb
  · exact hr
  · exact False.elim (hNotLeft hl)
  · exact False.elim (hNotRight hb)

/-- An actual FULL native embedded source piece whose entire
weak image is in the FULL target common seam has a genuine
weak EHN factorization through X. Merely set-theoretic image
containment is upgraded using native irreducible source tests
and cancellation along the FULL target-root embedding. -/
theorem fullNativePiece_weakEHN_factors_intoFullCommonRoot
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
    (hNotLeft : ∀ q : Q, iQ q ∉ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) flip)
    (hNotRight : ∀ q : Q, iQ q ∉ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) flip) :
    ∃ p : Q → UX,
      Piece.IsEHNHomomorphismEmbedding X p ∧
      ∀ q : Q, (jLeft.comp iLeft) (p q) = flip (iQ q) := by
  have hQEHN : Piece.IsEHNHomomorphismEmbedding Target
      (fun q : Q => flip (iQ q)) :=
    hFlip.comp iQ.isEHNHomomorphismEmbedding
  have hQImage : ∀ q : Q,
      ∃ r : UX, flip (iQ q) = (jLeft.comp iLeft) r := by
    intro q
    obtain ⟨r, hr⟩ :=
      weakFree_noExclusive_isSharedRoot
        Target Left Right X iLeft iRight jLeft jRight
        hFree flip (iQ q) (hNotLeft q) (hNotRight q)
    exact ⟨r, hr.symm⟩
  exact ehnHomomorphismEmbedding_factor_full_side
    hQEHN (jLeft.comp iLeft) hQImage

/-- Rooted specialization of the necessary common-root factor:
if each selected Q root already maps to the full seam, EVERY
private Q nonroot is A-inactive, and EVERY Q source vertex is
B-inactive, then the entire genuine Q admits an EHN map into X.

For a selected Q arising from the verified right-to-left flip,
the no-new-B and root-seam premises are supplied by the original
source replacement, but the PRIVATE A-neutrality premise is
NOT automatically available. -/
theorem fullNativeRootedPiece_Aneutral_noB_factors_intoFullCommonRoot
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
    (hNoAPrivate : ∀ q : Q,
      q ∉ Set.range roots →
      flip (iQ q) ∉ fullFreeLeftExclusiveTarget iLeft jLeft)
    (hNoBFromQ : ∀ q : Q,
      flip (iQ q) ∉ fullFreeRightExclusiveTarget iRight jRight) :
    ∃ p : Q → UX,
      Piece.IsEHNHomomorphismEmbedding X p ∧
      ∀ q : Q, (jLeft.comp iLeft) (p q) = flip (iQ q) := by
  have hNotLeft : ∀ q : Q,
      iQ q ∉ weakFreeLeftPart
        (sL := iLeft) (iL := jLeft) flip := by
    intro q hLeft
    by_cases hRoot : q ∈ Set.range roots
    · obtain ⟨r, hr⟩ := hRoot
      apply hLeft.2
      change flip (iQ q) ∈ Set.range (jLeft.comp iLeft)
      simpa only [hr] using hRootSeam r
    · apply hNoAPrivate q hRoot
      exact (weakFreeLeftPart_iff_targetExclusive
        iLeft jLeft flip (iQ q)).mp hLeft
  have hRootTargetAgree : ∀ r : UX,
      jRight (iRight r) = jLeft (iLeft r) := by
    intro r
    exact ((hFree.overlap (iLeft r) (iRight r)).mpr
      ⟨r, rfl, rfl⟩).symm
  have hNotRight : ∀ q : Q,
      iQ q ∉ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) flip := by
    intro q hRight
    have hRightSwapped :
        iQ q ∈ weakFreeLeftPart
          (sL := iRight) (iL := jRight) flip := by
      refine ⟨hRight.1, ?_⟩
      intro hRootR
      obtain ⟨r, hr⟩ := hRootR
      apply hRight.2
      exact ⟨r, (hRootTargetAgree r).symm.trans hr⟩
    exact hNoBFromQ q
      ((weakFreeLeftPart_iff_targetExclusive
        iRight jRight flip (iQ q)).mp hRightSwapped)
  exact fullNativePiece_weakEHN_factors_intoFullCommonRoot
    Piece New Target Left Right X
    iLeft iRight jLeft jRight hFree iQ flip hFlip
    hNotLeft hNotRight

/-- Under the actual full target free amalgam and no-new-B
condition, **private A-neutrality is equivalent to existence of
an exact EHN factorization of the ENTIRE selected rooted Q into
the FULL common root X, with the original target map unchanged**.

The reverse implication needs only exact target coordinate
agreement, not injectivity of the weak map and not any
forbidden-family closure. This is a structural IFF for the
selected-Q neutrality hypothesis of original Claim 2. -/
theorem fullNativeRootedPiece_Aneutral_iff_exactEHNFullRootFactor
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
      flip (iQ q) ∉ fullFreeRightExclusiveTarget iRight jRight) :
    (∀ q : Q, q ∉ Set.range roots →
      flip (iQ q) ∉ fullFreeLeftExclusiveTarget iLeft jLeft) ↔
    (∃ p : Q → UX,
      Piece.IsEHNHomomorphismEmbedding X p ∧
      ∀ q : Q, (jLeft.comp iLeft) (p q) = flip (iQ q)) := by
  constructor
  · intro hNeutral
    exact fullNativeRootedPiece_Aneutral_noB_factors_intoFullCommonRoot
      Piece New Target Left Right X
      iLeft iRight jLeft jRight hFree iQ flip hFlip
      roots hRootSeam hNeutral hNoBFromQ
  · rintro ⟨p, _hQEHN, hSame⟩ q _hNonroot hA
    have hWeakLeft :
        iQ q ∈ weakFreeLeftPart
          (sL := iLeft) (iL := jLeft) flip :=
      (weakFreeLeftPart_iff_targetExclusive
        iLeft jLeft flip (iQ q)).mpr hA
    apply hWeakLeft.2
    exact ⟨p q, hSame q⟩

end AllThoseRamseyClasses.Lifts
