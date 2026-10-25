import AllThoseRamseyClasses.Lifts.SingletonOldRootProperRightFlip
import AllThoseRamseyClasses.Lifts.WeakRightBoundaryCoverage
import AllThoseRamseyClasses.Lifts.ConnectedForbiddenPositivePiece

/-!
# One-step right-support descent at any smallest mixed piece with singleton OLD root

The printed Section 3 Claim 2 faces a boundary-coverage dichotomy.
Suppose a finite connected forbidden weak EHN witness minimizes its
LEFT-exclusive SOURCE support and contains an actual mixed geometric
piece P of minimum NONROOT component size. Assume the OLD separating
root of P contains at most one source vertex, and the original map
is injective only on the full common-root preimage S.

Choose any right-exclusive S-component with a vertex x in P's selected
component. Let T be its complete generated external boundary, and let
a be the left-exclusive vertex already supplied by P's mixedness.
The original source, not an image quotient, determines two cases.

* If the component of a after deleting T covers all of T, the verified
  arbitrary-width direct B-to-A component flip applies; root images
  are injective because T is a subset of S.
* If coverage fails, the exact opposite-boundary construction captures
  the unique old root, and the singleton-old-root proper one-sided-piece
  theorem produces an actual right-only PROPER sub-piece of P. Its
  genuine original-global B-to-A flip again decreases right support.

Thus EVERY such choice admits a literal forbidden replacement with
STRICTLY fewer right-exclusive SOURCE vertices; no external boundary
partner or coverage assumption remains.

This is NOT a contradiction to LEFT-support minimality: successful
B-to-A flips may increase left support, and the outer mixed piece is
not yet known to survive the replacement. No witness is assumed to
minimize left and right support simultaneously.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under the original LEFT support minimum, global minimum of
nonroot mixed-piece size, injection on the full common-root
preimage, and a singleton OLD mixed-piece root, ANY chosen
right-exclusive S-component lying inside that old piece
admits a literal B-to-A forbidden-source flip STRICTLY lowering
original RIGHT-exclusive source support.

Both covered and uncovered boundary cases are proved, not assumed.
The conclusion does not claim a strictly lower LEFT-support count. -/
theorem minimalLeftSingletonOldRoot_alwaysCanDecreaseRight
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
    (hMinLeft : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft))
    (hInjOnRoot : Set.InjOn w.toTarget
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget))
    (P : MixedGeometricPiece w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget))
    (hMinP : ∀ Q : MixedGeometricPiece w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget),
      P.nonrootCount ≤ Q.nonrootCount)
    (hSingletonOldRoot : ∀ a b : w.Carrier,
      a ∈ Set.range P.data.roots →
      b ∈ Set.range P.data.roots → a = b)
    (x : {z : w.Carrier // z ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
    (hxOld : x.1 ∈ functionalComponentFrom w.source
      (Set.range P.data.roots) P.data.left) :
    ∃ (V' : Type) (New : Structure L V'),
      F New ∧
      ∃ flip : V' → UT,
        New.IsEHNHomomorphismEmbedding Target flip ∧
        Nat.card {v : V' //
          flip v ∈ fullFreeRightExclusiveTarget iRight jRight} <
        Nat.card {v : w.Carrier //
          w.toTarget v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  letI : Finite w.Carrier := w.finiteCarrier
  let S : Set w.Carrier :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget
  let T : Set w.Carrier :=
    w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph S x))
  have hSclosed : w.source.IsClosed S :=
    weakFreeRootPart_isClosed
      (sL := iLeft) (iL := jLeft)
      w.toTarget w.homEmbedding.1
  have hTS : T ⊆ S :=
    functionalClosure_neighborhood_subset_cut
      w.source S hSclosed x
  obtain ⟨a, haOld, haLeft⟩ := P.left_mixed
  have haNotT : a ∉ T := by
    intro haT
    exact haLeft.2 (hTS haT)
  let y : {z : w.Carrier // z ∉ T} := ⟨a, haNotT⟩
  have hPath : ReachOutside w.source.graph (∅ : Set w.Carrier)
      (⟨x.1, by simp⟩ : {z : w.Carrier // z ∉ ∅})
      (⟨a, by simp⟩ : {z : w.Carrier // z ∉ ∅}) :=
    gaifmanPath_to_emptyCutReach w.source
      ((hConnected w.source w.finiteCarrier w.forbidden).2 x.1 a)
  by_cases hCoverage : T ⊆ w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph T y))
  · have hCoverageAll :
        ∀ y' : {z : w.Carrier // z ∉ T}, y'.1 = a →
          T ⊆ w.source.functionClosure
            (gaifmanNeighborhood w.source.graph
              (componentFrom w.source.graph T y')) := by
      intro y' hYa
      have hEq : y' = y := Subtype.ext hYa
      simpa only [hEq] using hCoverage
    have hInjT : Set.InjOn w.toTarget T := by
      intro u hu v hv huv
      exact hInjOnRoot (hTS hu) (hTS hv) huv
    exact rightComponent_oppositeCoverage_strictRightSupport
      F hFiniteF w.source w.finiteCarrier w.forbidden
      Target w.toTarget w.homEmbedding
      Left Right jLeft jRight X iLeft iRight
      hFree hCommon x hxRight
      T rfl hTS a haLeft hCoverageAll hPath hInjT
  · obtain ⟨m, Qright, hm, hRootExact, hProper, hNoLeft,
        V', New, hNew, flip, hFlip, hDrop⟩ :=
      minimalLeftSingletonOldRoot_uncovered_hasProperRightFlip
        F hFiniteF hConnected
        Target Left Right jLeft jRight X iLeft iRight
        hFree hCommon w hMinLeft hInjOnRoot
        P hMinP hSingletonOldRoot
        x hxRight hxOld T rfl hTS
        y haLeft haOld hCoverage
    exact ⟨V', New, hNew, flip, hFlip, hDrop⟩

end AllThoseRamseyClasses.Lifts
