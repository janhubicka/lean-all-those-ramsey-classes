import AllThoseRamseyClasses.Lifts.FunctionalComponentFreeAmalgam
import AllThoseRamseyClasses.Lifts.ArbitraryFunctionalFreeFold
import AllThoseRamseyClasses.Lifts.CommonLiftFlipStrictSupport

/-!
# Strict support decrease by folding an arbitrary CLOSED-root component

The difficult second geometric Claim 2 of the printed 2019 proof
arises from insisting that an indexed forbidden piece have a
MINIMAL separating root.

There is a different option for bounded-size forbidden families:
record weak realizations of ALL genuine induced components over
arbitrary FUNCTION-CLOSED vertex roots, not just minimal ones.
For the closed preimage S = f^{-1}(X) in a target free amalgam,
the full native piece S ∪ C of ANY A-only Gaifman component
C of Source minus S is already entirely on the A-side.

This module verifies the purely functional SOURCE-side flip with
such a nonminimal closed root R. If the SAME induced full piece
over R has a weak EHN realization in the target B-side with
matching root images, fold that map and the unchanged old
complement along the ACTUAL free-amalgam decomposition of
the original source. The original forbidden SOURCE IS UNCHANGED.
The new EHN map has strictly fewer A-only SOURCE vertices.

No minimal separator, quotient image, root-image injectivity,
or forbidden-image closure is assumed. The separate construction
of a finite-index expanded language recording all such pieces
is NOT proved here and may require bounded forbidden sizes.
The unrestricted published Section 3 theorem remains open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An actual finite functional source admits a strictly smaller
A-only SOURCE-support weak EHN map into the SAME target free
amalgam whenever one arbitrary function-closed-root component
has a rooted realization in Right.

The source remains exactly Source: it is folded along its true
full functional component/free-complement diagram, rather than
replaced by a weak image or an equivalent forbidden structure.

In particular the root R need NOT be a minimal separating cut,
and pRight may identify distinct root vertices in the target. -/
theorem closedComponent_rightRealization_strict_leftSupport
    {V UX UA UB UT : Type}
    [Finite V]
    (Source : Structure L V)
    (R : Set V)
    (hR : Source.IsClosed R)
    (root : {v : V // v ∉ R})
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (pRight : functionalComponentUnion Source R root → UB)
    (hpRight :
      (functionalComponentInduce Source R hR root).IsEHNHomomorphismEmbedding
        Right pRight)
    (hRoot : ∀ r : R,
      jRight (pRight (componentRootToPiece Source R hR root r)) =
        f r.1)
    (oldVertex : V)
    (hvComponent :
      oldVertex ∈ functionalComponentFrom Source R root)
    (hvLeft :
      f oldVertex ∈ fullFreeLeftExclusiveTarget iLeft jLeft) :
    ∃ flip : V → UT,
      Source.IsEHNHomomorphismEmbedding Target flip ∧
      (∀ b : (Set.compl (functionalComponentFrom Source R root)),
        flip b.1 = f b.1) ∧
      Nat.card {v : V //
        flip v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} <
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
  classical
  let P := functionalComponentInduce Source R hR root
  let T := functionalComponentComplementInduce Source R hR root
  let iP := functionalComponentEmbedding Source R hR root
  let iT := functionalComponentComplementEmbedding Source R hR root
  let sP := componentRootToPiece Source R hR root
  let sT := componentRootToComplement Source R hR root
  have hSourceFree :
      Structure.IsFreeAmalgam sP sT iP iT :=
    component_isFreeAmalgam Source R hR root
  let pP : P.Carrier → UT := jRight ∘ pRight
  let pT : T.Carrier → UT := fun b => f b.1
  have hpP : P.IsEHNHomomorphismEmbedding Target pP :=
    jRight.isEHNHomomorphismEmbedding.comp hpRight
  have hpT : T.IsEHNHomomorphismEmbedding Target pT :=
    hf.comp iT.isEHNHomomorphismEmbedding
  have hCompat : ∀ r : R,
      pP (sP r) = pT (sT r) := by
    intro r
    exact hRoot r
  let flip : V → UT :=
    compatibleFunctionalFold hSourceFree pP pT hCompat
  have hFlip : Source.IsEHNHomomorphismEmbedding Target flip :=
    compatibleFunctionalFold_isEHNHomomorphismEmbedding
      hSourceFree pP pT hCompat hpP hpT
  have hP : ∀ a : P.Carrier,
      flip (iP a) = jRight (pRight a) := by
    intro a
    exact compatibleFunctionalFold_left
      hSourceFree pP pT hCompat a
  have hT : ∀ b : T.Carrier,
      flip (iT b) = f b.1 := by
    intro b
    exact compatibleFunctionalFold_right
      hSourceFree pP pT hCompat b
  let AOnly : Set UT := fullFreeLeftExclusiveTarget iLeft jLeft
  have hNoLeft : ∀ a : P.Carrier,
      flip (iP a) ∉ AOnly := by
    intro a
    rw [hP a]
    exact freeRight_avoids_fullLeftExclusiveTarget
      iLeft iRight jLeft jRight hTargetFree (pRight a)
  letI : Fintype V := Fintype.ofFinite V
  letI : Finite T.Carrier :=
    Finite.of_injective (fun b : T.Carrier => b.1) (by
      intro a b hab
      exact Subtype.ext hab)
  letI : Fintype T.Carrier := Fintype.ofFinite T.Carrier
  have hOldT : ∀ b : T.Carrier,
      f (iT b) = pT b := by
    intro b
    rfl
  have hNewT : ∀ b : T.Carrier,
      flip (iT b) = pT b := hT
  have hOutside : ∀ b : T.Carrier,
      oldVertex ≠ iT b := by
    intro b hb
    have hv : oldVertex = b.1 := hb
    have hbComp : b.1 ∈
        functionalComponentFrom Source R root :=
      hv ▸ hvComponent
    exact b.2 hbComp
  have hStrict :
      Nat.card {v : V // flip v ∈ AOnly} <
      Nat.card {v : V // f v ∈ AOnly} := by
    exact flipExclusiveSupport_strict_decrease
      (iOldR := iT)
      (iNewL := iP)
      (iNewR := iT)
      (sNewL := sP)
      (sRight := sT)
      hSourceFree f flip pT hOldT hNewT
      AOnly hNoLeft oldVertex hvLeft hOutside
  refine ⟨flip, hFlip, ?_, hStrict⟩
  intro b
  exact hT b

end AllThoseRamseyClasses.Lifts
