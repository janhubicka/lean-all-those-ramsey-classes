import AllThoseRamseyClasses.Lifts.SingletonBoundaryProperRightDescent
import AllThoseRamseyClasses.Lifts.ForbiddenWeakWitnessMinimization
import AllThoseRamseyClasses.Lifts.ConnectedForbiddenPositivePiece

/-!
# Actual right-support minimality contradiction in the singleton-boundary case

This is a genuine Section 3 Claim 2 special-case contradiction.
For a connected finite forbidden-source EHN witness into an actual
full functional free amalgam of two F-free witnesses with their
common FULL original global canonical lift, choose a source map
minimizing its number of right-exclusive SOURCE vertices.

Such a minimizer cannot have a genuine mixed old source piece P
whose selected component contains a right-exclusive S-component
and a left-exclusive source vertex, if that right component has
generated external boundary of cardinality at most ONE.

The connected source supplies the path, verified component geometry
constructs the partner, the singleton forces distinct target roots,
and the genuine B-to-A forbidden-source replacement STRICTLY lowers
right support. No quotient injectivization or independent new-piece
hypothesis occurs.

This is not the original unrestricted Claim 2: the printed first
minimality chooses LEFT rather than RIGHT support, and larger,
possibly noninjective root boundaries remain open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A finite forbidden-source witness minimizing ORIGINAL RIGHT
support cannot contain a selected right-exclusive component
with singleton generated boundary inside a mixed old piece.

All geometry and replacement are constructed, starting from
the real native EHN witness and FULL original canonical lifts. -/
theorem minimalRightWitness_noSingletonBoundaryMixedPiece
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (w : ForbiddenEHNWitness F Target)
    (hMinRight : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight) ≤
        v.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight))
    {n : ℕ} (P : GeometricFunctionalPieceData w.source n)
    (hRoots : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
    (x : {z : w.Carrier // z ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget})
    (hxOld : x.1 ∈ functionalComponentFrom w.source
      (Set.range P.roots) P.left)
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
    (T : Set w.Carrier)
    (hT : T = w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget) x)))
    (hTS : T ⊆ weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
    (hSingleton : ∀ u v : w.Carrier, u ∈ T → v ∈ T → u = v)
    (a : w.Carrier)
    (haOld : a ∈ functionalComponentFrom w.source
      (Set.range P.roots) P.left)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) w.toTarget) :
    False := by
  have hPath : ReachOutside w.source.graph (∅ : Set w.Carrier)
      (⟨x.1, by simp⟩ : {z : w.Carrier // z ∉ ∅})
      (⟨a, by simp⟩ : {z : w.Carrier // z ∉ ∅}) :=
    gaifmanPath_to_emptyCutReach w.source
      ((hConnected w.source w.finiteCarrier w.forbidden).2 x.1 a)
  obtain ⟨m, Q, hQroot, hProper, V', New, hNew, flip, hFlip, hDrop⟩ :=
    singletonBoundary_properRightPiece_strictSupport
      F hFiniteF w.source w.finiteCarrier w.forbidden
      Target w.toTarget w.homEmbedding
      Left Right jLeft jRight X iLeft iRight
      hFree hCommon P hRoots x hxOld hxRight
      T hT hTS hSingleton a haOld haLeft hPath
  let replacement : ForbiddenEHNWitness F Target := {
    Carrier := V'
    finiteCarrier := hFiniteF New hNew
    source := New
    forbidden := hNew
    toTarget := flip
    homEmbedding := hFlip
  }
  have hStrict :
      replacement.sourceSupportCount
        (fullFreeRightExclusiveTarget iRight jRight) <
      w.sourceSupportCount
        (fullFreeRightExclusiveTarget iRight jRight) := hDrop
  exact (minimalForbiddenEHNWitness_no_strict_drop
    (fullFreeRightExclusiveTarget iRight jRight)
    w hMinRight replacement) hStrict

end AllThoseRamseyClasses.Lifts
