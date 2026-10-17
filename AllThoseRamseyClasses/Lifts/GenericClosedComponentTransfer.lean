import AllThoseRamseyClasses.Lifts.FiniteClosedComponentTagLift
import AllThoseRamseyClasses.Lifts.WholeCommonRootComponentFactor
import AllThoseRamseyClasses.Lifts.NonminimalClosedComponentFlip

/-!
# Componentwise transfer as the minimal interface for nonminimal folded flips

This isolates the EXACT relational transfer required to retarget a
complete function-closed-root component. It only asks that each
actual tagged component-pattern realization in Left with roots
in X yields a realization of the SAME pattern in Right.
A common FULL all-component lift supplies this relation transfer,
but the theorem below needs no additional expansion structure.

The source remains literally unchanged under the flip; no
minimal separator, root-image injectivity, or forbidden quotient
is required. A finite-family tagged lift can establish this
transfer for each of its finitely many named forbidden sources.

No maximal-lift existence or free-amalgamation theorem is
asserted in this module.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Minimal semantic interface for reusing all closed-root component
relations across the full common old shadow X. This is only
forward transfer, as needed for the flip. Root images may collide. -/
def AllClosedComponentRootedTransfer
    {V UX UA UB : Type}
    [Finite V] (Source : Structure L V)
    (X : Structure L UX)
    (Left : Structure L UA)
    (Right : Structure L UB)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right) : Prop :=
  ∀ (tag : ClosedComponentTag Source)
    (xs : Fin tag.width → UX),
    FunctionalRootRealization tag.rootedPattern Left
      (iLeft ∘ xs) →
    FunctionalRootRealization tag.rootedPattern Right
      (iRight ∘ xs)

/-- Direct strict source-support descent under the new finite
ALL-CLOSED-COMPONENT folded canonical lift.

The source is literally unchanged, including all complete old
functional interpretations; only its weak target map changes.
This requires NO assumption about the number of B-only source
components, no minimal separating root, and no weak root-image
injectivity. -/
theorem wholeComponent_strict_leftSupport_of_rootedTransfer
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
    (hTransfer : AllClosedComponentRootedTransfer
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
  have hRealLeft :
      FunctionalRootRealization tag.rootedPattern Left
        (iLeft ∘ xs) :=
    ⟨pLeft, hpLeft, hRootTuple⟩
  obtain ⟨pRight, hpRight, hRootRight⟩ :=
    hTransfer tag xs hRealLeft
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
