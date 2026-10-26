import AllThoseRamseyClasses.Lifts.GlobalRightToLeftPieceFlip

/-!
# Original outer root coordinates survive an actual B-to-A source flip

The printed Section 3 Claim 2 repeatedly flips a one-sided
proper sub-piece inside a fixed larger mixed forbidden-source
piece. The full contextual rooted-piece transport is still open.
One key part of that invariant DOES follow directly from the
verified original-global full functional free-amalgam diagram:

A genuine B-to-A source replacement keeps the entire complementary
source structure embedded FULLY in the new forbidden source,
and the new EHN target map agrees EXACTLY with the old map on that
complement. Therefore EVERY chosen old outer root vertex which lies
outside the FLIPPED nonroot component survives by an injective
root tuple, with precisely its original target image.

The statement is not just an equality of target root images:
it exports a FULL embedding of the unchanged native functional
complement, including all relation incidences and partial
function fibres. No quotient of the original weak map or
artificial change of forbidden family is made.

It does NOT assert that a transported outer piece is a genuine
minimal-closed-separator piece, that its incompatibility class
is preserved, or that repeated flips terminate inside it.
These are the remaining contextual/congruence obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- When all vertices of a chosen outer geometric piece's OLD
ordered root lie outside the selected component of an inner
positive-width B-only piece, an ACTUAL full-global B-to-A
forbidden-source flip preserves the complete old complement
by a FULL embedding, and preserves the old outer root tuple
injectively with its EXACT original target coordinates.

The original source-to-target EHN map itself may be globally
noninjective; only the FLIPPED inner root images must be
injective for the canonical lifted relation to be usable. -/
theorem geometricGlobalRightFlip_preserves_outerRootCoordinates
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Forbidden n)
    (d : GeometricFunctionalPieceData Forbidden m)
    (hm : 0 < m)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hInnerRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hInnerNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hInnerRootInjective : Function.Injective
      (fun i : Fin m => f (d.roots i)))
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left) :
    ∃ (V' : Type) (New : Structure L V'),
      F New ∧
      ∃ (iComplement : Structure.Embedding
          (geometricGlobalComplementChart Forbidden d).str New)
        (flip : V' → UT),
        New.IsEHNHomomorphismEmbedding Target flip ∧
        (∀ b : (geometricGlobalComplementChart Forbidden d).Carrier,
          flip (iComplement b) = f b.1) ∧
        ∃ rootAfter : Fin n → V',
          Function.Injective rootAfter ∧
          ∀ i : Fin n, flip (rootAfter i) = f (P.roots i) := by
  let Compl := geometricGlobalComplementChart Forbidden d
  obtain ⟨Q, _hEquivalent, g, _hg,
      V', New, hNew, _iQ, iT, _hFreeNew,
      flip, hFlip, _hQImage, hTImage⟩ :=
    geometricGlobalCommonFullLiftFlip_rightToLeft
      F Forbidden hFinite hForbidden
      d hm Target f hf
      Left Right jLeft jRight X iLeft iRight
      hFree hCommon hInnerRoots hInnerNoLeft
      hInnerRootInjective
  let rootAfter : Fin n → V' :=
    fun i => iT
      (⟨P.roots i, hOuterRootOutside i⟩ : Compl.Carrier)
  have hRootInjective : Function.Injective rootAfter := by
    intro i j hij
    apply P.roots_injective
    have hSame :
        (⟨P.roots i, hOuterRootOutside i⟩ : Compl.Carrier) =
        ⟨P.roots j, hOuterRootOutside j⟩ :=
      iT.injective hij
    exact congrArg Subtype.val hSame
  have hRootImages :
      ∀ i : Fin n, flip (rootAfter i) = f (P.roots i) := by
    intro i
    exact hTImage
      (⟨P.roots i, hOuterRootOutside i⟩ : Compl.Carrier)
  exact ⟨V', New, hNew, iT, flip, hFlip, hTImage,
    rootAfter, hRootInjective, hRootImages⟩

end AllThoseRamseyClasses.Lifts
