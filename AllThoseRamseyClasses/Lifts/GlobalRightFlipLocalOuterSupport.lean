import AllThoseRamseyClasses.Lifts.GlobalFlipLocalRightSupport
import AllThoseRamseyClasses.Lifts.GlobalFlipOuterRootStrictSupport

/-!
# One literal B→A forbidden flip with strict LOCAL outer-context support drop

The original 2019 Claim 2 uses a globally minimal mixed source piece P
and repeatedly attempts to flip a proper right-only inner geometric
source piece d to the other target side.

The previously verified original-global canonical lift flip gives an
ACTUAL new finite forbidden source New=Q⊕_U E, a compatible EHN target
map, and an exact full embedding of the old inner complement E.
The actual global right-exclusive source support strictly decreases,
as in the independently verified GlobalFlipOuterRootStrictSupport.

For an inner piece WHOSE ENTIRE SOURCE VERTEX SET belongs to P,
the new contextual-support theorem proves a stronger conclusion on
the SAME replacement source, not on separately chosen existential
witnesses: the number of vertices mapped B-only INSIDE the
transported outer context Q ∪ (E∩P) decreases strictly.

The transported context is native function-closed and contains the
old outer root when that root is contained in E. It is NOT yet
proved to be a genuine connected minimal-separator geometric piece
or to preserve the complete rooted incompatibility profile.
Those remain essential obligations for iterating Claim 2 and
discharging the unrestricted Section 3 theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- One actual literal canonical B-to-A flip of a proper inner
source piece strictly decreases the ORIGINAL right-exclusive
source count INSIDE the transported outer context.

The same New, full native source embeddings, free-amalgam
certificate and EHN target map witness every conclusion.

Only injectivity of the flipped INNER root's target image is
needed; the forbidden weak map may collide elsewhere. -/
theorem geometricGlobalRightFlip_strictLocalOuterSupport
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Forbidden n)
    (d : GeometricFunctionalPieceData Forbidden m)
    (hm : 0 < m)
    (hInnerInside :
      geometricPieceVertices Forbidden d ⊆
        geometricPieceVertices Forbidden P)
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
    (oldVertex : V)
    (hvComponent : oldVertex ∈
      functionalComponentFrom Forbidden (Set.range d.roots) d.left)
    (hvRight : oldVertex ∈
      weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f) :
    ∃ (V' : Type) (New : Structure L V'),
      F New ∧
      ∃ (Q : FunctionalRootExtension
          (geometricGlobalFunctionalChart Forbidden d).root)
        (iQ : Structure.Embedding Q.str New)
        (iE : Structure.Embedding
          (geometricGlobalComplementChart Forbidden d).str New),
        Structure.IsFreeAmalgam
          Q.rootEmbedding
          (geometricGlobalComplementChart Forbidden d).rootEmbedding
          iQ iE ∧
        ∃ flip : V' → UT,
          New.IsEHNHomomorphismEmbedding Target flip ∧
          (∀ b : (geometricGlobalComplementChart Forbidden d).Carrier,
            flip (iE b) = f b.1) ∧
          Nat.card {w : V' //
            w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪
              iE '' oldOuterContextInInnerComplement Forbidden P d) ∧
            flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
          Nat.card {v : V //
            v ∈ geometricPieceVertices Forbidden P ∧
            f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  classical
  let Compl := geometricGlobalComplementChart Forbidden d
  obtain ⟨Q, _hEq, g, _hg, V', New, hNew,
      iQ, iE, hNewFree, flip, hFlip, hQImage, hEImage⟩ :=
    geometricGlobalCommonFullLiftFlip_rightToLeft
      F Forbidden hFinite hForbidden d hm
      Target f hf
      Left Right jLeft jRight X iLeft iRight
      hFree hCommon hInnerRoots hInnerNoLeft hInnerRootInjective
  let oldCompl : Structure.Embedding Compl.str Forbidden :=
    functionalComponentComplementEmbedding Forbidden
      (Set.range d.roots) d.minimal.1 d.left
  letI : Fintype V := Fintype.ofFinite V
  letI : Finite V' := hFiniteF New hNew
  letI : Fintype V' := Fintype.ofFinite V'
  letI : Finite Compl.Carrier :=
    Finite.of_injective (fun b : Compl.Carrier => b.1) (by
      intro a b hab
      exact Subtype.ext hab)
  letI : Fintype Compl.Carrier := Fintype.ofFinite Compl.Carrier
  have hOldComplement : ∀ b : Compl.Carrier,
      f (oldCompl b) = f b.1 := by
    intro b
    rfl
  have hOutside : ∀ b : Compl.Carrier,
      oldVertex ≠ oldCompl b := by
    intro b hb
    have hv : oldVertex = b.1 := hb
    have hbC : b.1 ∈ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left := hv ▸ hvComponent
    exact b.2 hbC
  have hNewPieceAvoid : ∀ a : Q.Carrier,
      flip (iQ a) ∉
        fullFreeRightExclusiveTarget iRight jRight := by
    intro a
    rw [hQImage a]
    exact freeRight_avoids_fullLeftExclusiveTarget
      iRight iLeft jRight jLeft hFree.swap (g a)
  have hTargetAgreeR (r : UX) :
      jRight (iRight r) = jLeft (iLeft r) :=
    ((hFree.overlap (iLeft r) (iRight r)).mpr
      ⟨r, rfl, rfl⟩).symm
  have hvRightSwapped :
      oldVertex ∈ weakFreeLeftPart
        (sL := iRight) (iL := jRight) f := by
    refine ⟨hvRight.1, ?_⟩
    intro hr
    obtain ⟨x, hx⟩ := hr
    apply hvRight.2
    exact ⟨x, (hTargetAgreeR x).symm.trans hx⟩
  have hvRightTarget :
      f oldVertex ∈ fullFreeRightExclusiveTarget
        iRight jRight :=
    (weakFreeLeftPart_iff_targetExclusive
      iRight jRight f oldVertex).mp hvRightSwapped
  have hGlobalDrop :
      Nat.card {w : V' //
        flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
      Nat.card {v : V //
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
    exact flipExclusiveSupport_strict_decrease
      (iOldR := oldCompl)
      (iNewL := iQ)
      (iNewR := iE)
      (sNewL := Q.rootEmbedding)
      (sRight := Compl.rootEmbedding)
      hNewFree f flip (fun b : Compl.Carrier => f b.1)
      hOldComplement hEImage
      (fullFreeRightExclusiveTarget iRight jRight)
      hNewPieceAvoid oldVertex hvRightTarget hOutside
  have hLocalDrop :=
    geometricInnerSubpiece_strict_localRightSupport_of_global
      Forbidden P d hInnerInside Q New iQ iE
      hNewFree f flip
      (fullFreeRightExclusiveTarget iRight jRight)
      hEImage hGlobalDrop
  exact ⟨V', New, hNew, Q, iQ, iE, hNewFree,
    flip, hFlip, hEImage, hLocalDrop⟩

end AllThoseRamseyClasses.Lifts
