import AllThoseRamseyClasses.Lifts.ClosedComponentCommonFullLift
import AllThoseRamseyClasses.Lifts.WholeCommonRootComponentFactor
import AllThoseRamseyClasses.Lifts.NonminimalClosedComponentFlip

/-!
# Strict A-only support descent from a common FULL all-component tagged lift

This is the main conditional payoff of recording ALL genuine
closed-root components, rather than only the printed 2019
minimal-separator pieces.

Given a finite native source with weak EHN map f into a full target
free amalgam D=A⊕_X B, and a shared FULL induced auxiliary tagged
lift of X inside the ALL-COMPONENT canonical lifts of A and B
for that very source type, ANY A-only source vertex x yields
a STRICTLY LOWER A-only source-support weak EHN map of the
SAME unchanged source into D.

Proof ingredients:
1. S=f^{-1}(X) is function-closed, and the ENTIRE component
   C of Source minus S containing x maps to A-only;
2. its full native piece S∪C weakly factors into A and its
   complete ordered root tuple factors through X;
3. the true all-components canonical relation of that piece
   holds in A, hence in B by equality of the SAME fully
   induced tagged expansion on X;
4. obtain a weak realization of the SAME true piece in B,
   allowing any collisions of root-image vertices;
5. the already verified arbitrary CLOSED-root component
   fold retargets the piece directly into B, preserving
   the whole old complement map and decreasing the A-only
   SOURCE vertex count strictly.

Neither geometric minimal cuts nor the multicomponent Claim 2,
incompatibility piece quotients, root-image injectivity or
forbidden-image normalizations are used.

This theorem is conditional on a common FULL all-components
tagged lift of the particular finite source. Its extension
to a finite list of forbidden isomorphism representatives
and the maximal-lift strong-amalgamation class theorem
remain separate tasks. The printed regular infinite-family
Section 3 proof is NOT claimed validated.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Direct strict source-support descent under the new finite
ALL-CLOSED-COMPONENT folded canonical lift.

The source is literally unchanged, including all complete old
functional interpretations; only its weak target map changes.
This requires NO assumption about the number of B-only source
components, no minimal separating root, and no weak root-image
injectivity. -/
theorem wholeComponentTaggedLift_strict_leftSupport
    {V UX UA UB UT : Type}
    [Finite V]
    (Source : Structure L V)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA)
    (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonAllClosedComponentLift
      Source X Left Right iLeft iRight)
    (x : V)
    (hx : x ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f) :
    ∃ flip : V → UT,
      Source.IsEHNHomomorphismEmbedding Target flip ∧
      Nat.card {v : V //
        flip v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} <
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
  classical
  let S : Set V :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) f
  let hS : Source.IsClosed S :=
    weakFreeRootPart_isClosed
      (sL := iLeft) (iL := jLeft) f hf.1
  let root : {z : V // z ∉ S} := ⟨x, hx.2⟩
  let tag : ClosedComponentTag Source := {
    cut := S
    closed := hS
    chosen := root
  }
  obtain ⟨pLeft, hpLeft, hPieceMap, xsX, hRootLeft⟩ :=
    weakSource_wholeCommonRootLeftComponent_factor
      hTargetFree f hf x hx
  let xs : Fin tag.width → UX :=
    fun i => xsX (tag.enumeration i)
  have hRootTuple : ∀ i : Fin tag.width,
      pLeft (tag.rootedPattern.root i) =
        iLeft (xs i) := by
    intro i
    exact hRootLeft (tag.enumeration i)
  obtain ⟨pRight, hpRight, hRootRight⟩ :=
    commonAllClosedComponentLift_rightWitness
      Source X Left Right iLeft iRight hCommon
      tag pLeft hpLeft xs hRootTuple
  have hTargetAgree (a : UX) :
      jLeft (iLeft a) = jRight (iRight a) :=
    (hTargetFree.overlap (iLeft a) (iRight a)).mpr
      ⟨a, rfl, rfl⟩
  have hRightRoot : ∀ r : S,
      jRight (pRight
        (componentRootToPiece Source S hS root r)) =
        f r.1 := by
    intro r
    obtain ⟨i, hi⟩ := tag.enumeration.surjective r
    subst r
    calc
      jRight (pRight
          (componentRootToPiece Source S hS root
            (tag.enumeration i))) =
          jRight (iRight (xs i)) :=
        congrArg jRight (hRootRight i)
      _ = jLeft (iLeft (xs i)) :=
        (hTargetAgree (xs i)).symm
      _ = jLeft (pLeft
          (componentRootToPiece Source S hS root
            (tag.enumeration i))) :=
        congrArg jLeft (hRootLeft (tag.enumeration i)).symm
      _ = f (tag.enumeration i).1 :=
        hPieceMap _
  have hOldComponent :
      x ∈ functionalComponentFrom Source S root :=
    functionalComponentFrom_root Source S root
  have hOldA :
      f x ∈ fullFreeLeftExclusiveTarget iLeft jLeft :=
    (weakFreeLeftPart_iff_targetExclusive
      iLeft jLeft f x).mp hx
  obtain ⟨flip, hFlip, _hUnchanged, hStrict⟩ :=
    closedComponent_rightRealization_strict_leftSupport
      Source S hS root Target f hf
      Left Right jLeft jRight X iLeft iRight hTargetFree
      pRight hpRight hRightRoot
      x hOldComponent hOldA
  exact ⟨flip, hFlip, hStrict⟩

end AllThoseRamseyClasses.Lifts
