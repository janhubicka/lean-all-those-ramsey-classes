import AllThoseRamseyClasses.Lifts.RightBoundaryPartnerPieceFactor
import AllThoseRamseyClasses.Lifts.GlobalRightToLeftStrictSupport
import AllThoseRamseyClasses.Lifts.ForbiddenWeakWitnessMinimization
import AllThoseRamseyClasses.Lifts.ConnectedForbiddenPositivePiece
import AllThoseRamseyClasses.Lifts.IrreducibleTestRootCollisions

/-!
# An arbitrary-width right component flips directly from an actual boundary partner

The genuine original-global B-to-A flip does not require choosing
an ambient smallest mixed forbidden-source piece P. Let S be the full
shared-root preimage of a weak EHN map to a real full functional free
amalgam, B a right-only component of Source minus S and
T = Cl_Source(N_Source(B)) ⊆ S its complete generated boundary.

If B has an actual minimal-closed-separator boundary partner
y outside T, x and y are connected in the original source and
the target weak map is injective ON T, we can directly:
  * construct a genuine positive-width source piece rooted at T,
    whose entire nonroot component is exactly B;
  * factor the native EHN map of that whole piece into Right;
  * apply the common FULL original quotient-indexed canonical lift,
    producing a NEW forbidden source with strictly smaller original
    right-exclusive SOURCE support.

There is no outer mixed piece, repeated-flip invariant, global
map injectivization, folded-root lift or artificial weak quotient.
For a right-support-minimal witness, an existing partner forces a
collision on the complete boundary T and failure of pairwise
irreducible-test coverage on T. Partner existence or root
injectivity are not inferred in the general-width case.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- One REAL right-only source component with an actual boundary partner,
positive separating root and injective target images ON that root
can be flipped directly, with strict ORIGINAL right-exclusive source
support decrease. No containing mixed piece P is required. -/
theorem rightComponent_partner_strictRightSupport
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V) (hForbidden : F Source)
    (Target : Structure L UT) (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (x : {z : V // z ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (T : Set V)
    (hT : T = Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))
    (hTS : T ⊆ weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (y : {z : V // z ∉ T})
    (hSep : ¬ ReachOutside Source.graph T (outsideCutMap hTS x) y)
    (hYBoundary : Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph T y)) = T)
    (hConnected : ReachOutside Source.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : V // z ∉ ∅}))
    (hInjT : Set.InjOn f T) :
    ∃ (V' : Type) (New : Structure L V'),
      F New ∧
      ∃ flip : V' → UT,
        New.IsEHNHomomorphismEmbedding Target flip ∧
        Nat.card {v : V' //
          flip v ∈ fullFreeRightExclusiveTarget iRight jRight} <
        Nat.card {v : V //
          f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  letI : Finite V := hFinite
  obtain ⟨n, d, hRoot, hRootS, hLeft, hRight, hComp,
      pRight, _hpRight, hMap⟩ :=
    weakRightComponent_boundaryPartner_hasGenuineFactor
      hFree f hf x hxRight T hT hTS y hSep hYBoundary
  have hPathD : ReachOutside Source.graph (∅ : Set V)
      (⟨d.left.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨d.right.1, by simp⟩ : {z : V // z ∉ ∅}) := by
    simpa only [hLeft, hRight] using hConnected
  have hn : 0 < n :=
    geometricPiece_positiveWidth_of_emptyCut_path Source d hPathD
  have hRootImageInjective :
      Function.Injective (fun i : Fin n => f (d.roots i)) := by
    intro i j hij
    apply d.roots_injective
    apply hInjT
    · rw [← hRoot]
      exact ⟨i, rfl⟩
    · rw [← hRoot]
      exact ⟨j, rfl⟩
    · exact hij
  have hNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f := by
    intro z hzC hzLeft
    let zP : geometricPieceVertices Source d :=
      ⟨z, Or.inr hzC⟩
    have hRightImage : f z = jRight (pRight zP) :=
      (hMap zP).symm
    exact (weakFreeLeftPart_not_right
      hFree f hzLeft (pRight zP)) hRightImage
  have hxComponent :
      x.1 ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left := by
    change x.1 ∈ componentFrom Source.graph
      (Set.range d.roots) d.left
    rw [hComp]
    exact componentFrom_root Source.graph
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x
  exact geometricGlobalCommonFullLiftFlip_strict_rightSupport
    F hFiniteF Source hFinite hForbidden
    d hn Target f hf Left Right jLeft jRight
    X iLeft iRight hFree hCommon hRootS hNoLeft
    hRootImageInjective x.1 hxComponent hxRight

/-- At a minimum of RIGHT-exclusive SOURCE support, any genuine
boundary partner of a right-exclusive component forces an actual
collision between DISTINCT source boundary vertices.
Consequently its boundary cannot be pairwise covered by
irreducible FULL source tests.

No selected outer mixed source piece is needed. The connectedness
of F supplies the whole-source x/y path used in the flip above. -/
theorem minimalRightWitness_partner_forcesBoundaryCollision
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
    (x : {z : w.Carrier // z ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
    (T : Set w.Carrier)
    (hT : T = w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget) x)))
    (hTS : T ⊆ weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
    (y : {z : w.Carrier // z ∉ T})
    (hSep : ¬ ReachOutside w.source.graph T
      (outsideCutMap hTS x) y)
    (hYBoundary : w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph T y)) = T) :
    (∃ u v : w.Carrier,
      u ∈ T ∧ v ∈ T ∧ u ≠ v ∧ w.toTarget u = w.toTarget v) ∧
      ¬ RootPairsCoveredByIrreducibleTests w.source T := by
  have hPath : ReachOutside w.source.graph (∅ : Set w.Carrier)
      (⟨x.1, by simp⟩ : {z : w.Carrier // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : w.Carrier // z ∉ ∅}) :=
    gaifmanPath_to_emptyCutReach w.source
      ((hConnected w.source w.finiteCarrier w.forbidden).2 x.1 y.1)
  have hNotInj : ¬ Set.InjOn w.toTarget T := by
    intro hInjT
    obtain ⟨V', New, hNew, flip, hFlip, hDecrease⟩ :=
      rightComponent_partner_strictRightSupport
        F hFiniteF w.source w.finiteCarrier w.forbidden
        Target w.toTarget w.homEmbedding
        Left Right jLeft jRight
        X iLeft iRight hFree hCommon
        x hxRight T hT hTS y hSep hYBoundary hPath hInjT
    let replacement : ForbiddenEHNWitness F Target := {
      Carrier := V'
      finiteCarrier := hFiniteF New hNew
      source := New
      forbidden := hNew
      toTarget := flip
      homEmbedding := hFlip
    }
    have hDrop :
        replacement.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) <
        w.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) := hDecrease
    exact (minimalForbiddenEHNWitness_no_strict_drop
      (fullFreeRightExclusiveTarget iRight jRight)
      w hMinRight replacement) hDrop
  constructor
  · classical
    by_contra hNoCollision
    apply hNotInj
    intro u hu v hv huv
    by_contra hneq
    exact hNoCollision ⟨u, v, hu, hv, hneq, huv⟩
  · intro hCovered
    apply hNotInj
    exact ehn_injOn_of_rootPairsCoveredByIrreducibleTests
      w.source Target w.toTarget w.homEmbedding T hCovered

end AllThoseRamseyClasses.Lifts
