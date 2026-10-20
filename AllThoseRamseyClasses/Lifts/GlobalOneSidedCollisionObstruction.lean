import AllThoseRamseyClasses.Lifts.GeometricIrreducibleRootImage
import Mathlib.Tactic

/-!
# The exact obstruction to original global Claim 1 for a one-sided piece

After the complete geometric one-sided EHN factorization and shared-root
coordinate reconstruction, Claim 1 proves that a support-minimal weak
forbidden witness with a one-sided positive-width selected piece
cannot have INJECTIVE root images.

The EHN full-irreducible-test clause separately proves injectivity
whenever the entire induced function-closed root is irreducible.
A one-coordinate root also has an injective image under every map.

Therefore any possible one-sided exceptional piece for the
root-INJECTIVE global canonical lift must have all three properties:

* two or more ordered root vertices;
* a REDUCIBLE induced closed root;
* a genuine collision of distinct root images in the target.

This is a substantial necessary-condition classification, not the
missing existence or quotient-normalization lemma. The printed
multicomponent Claim 2 and the unrestricted regular infinite-family
strong-amalgamation theorem are still open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An actual support-minimal forbidden map with a genuine
one-sided geometric source piece has a NONINJECTIVE target root
image. The derivation needs no independent auxiliary factorization
or root coordinates: the certified Claim 1 module constructs them.
-/
theorem minimalGlobalOneSidedPiece_rootImagesCollide
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (w : ForbiddenEHNWitness F Target)
    (hMin : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft))
    {n : ℕ}
    (d : GeometricFunctionalPieceData w.source n)
    (hn : 0 < n)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
    (hNoRight : ∀ z : w.Carrier,
      z ∈ functionalComponentFrom w.source (Set.range d.roots) d.left →
      z ∉ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
    (hLeft : d.left.1 ∈
      weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget) :
    ¬ Function.Injective (fun i : Fin n => w.toTarget (d.roots i)) := by
  intro hInjective
  exact minimalGlobalWitness_noOneSidedPiece_of_rootInjective
    F hFiniteF Target Left Right jLeft jRight
    X iLeft iRight hTargetFree hCommon w hMin
    d hn hRoots hNoRight hLeft hInjective

/-- The genuine remaining one-sided counterconfiguration in the
original global root-INJECTIVE lift is restricted to a WIDTH AT
LEAST TWO, a REDUCIBLE full closed source root, and a COLLISION
of ordered root images under the forbidden weak map.

These conclusions are proved rather than built into the statement
as hypotheses. No claim is made that such a configuration actually
occurs in an amalgam of compatible maximal witnesses.
-/
theorem minimalGlobalOneSidedPiece_hasReducibleCollidingRoot
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (w : ForbiddenEHNWitness F Target)
    (hMin : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft))
    {n : ℕ}
    (d : GeometricFunctionalPieceData w.source n)
    (hn : 0 < n)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
    (hNoRight : ∀ z : w.Carrier,
      z ∈ functionalComponentFrom w.source (Set.range d.roots) d.left →
      z ∉ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
    (hLeft : d.left.1 ∈
      weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget) :
    2 ≤ n ∧
      ¬ (w.source.induce (Set.range d.roots) d.minimal.1).Irreducible ∧
      ¬ Function.Injective
        (fun i : Fin n => w.toTarget (d.roots i)) := by
  have hCollision :
      ¬ Function.Injective
        (fun i : Fin n => w.toTarget (d.roots i)) :=
    minimalGlobalOneSidedPiece_rootImagesCollide
      F hFiniteF Target Left Right jLeft jRight
      X iLeft iRight hTargetFree hCommon w hMin
      d hn hRoots hNoRight hLeft
  have hNotIrr :
      ¬ (w.source.induce (Set.range d.roots) d.minimal.1).Irreducible := by
    intro hIrr
    exact hCollision
      (geometricRootImage_injective_of_irreducibleClosedRoot
        w.source d Target w.toTarget w.homEmbedding hIrr)
  have hNotOne : n ≠ 1 := by
    intro hOne
    exact hCollision
      (geometricRootImage_injective_widthOne w.source d w.toTarget hOne)
  have hWidth : 2 ≤ n := by omega
  exact ⟨hWidth, hNotIrr, hCollision⟩

end AllThoseRamseyClasses.Lifts
