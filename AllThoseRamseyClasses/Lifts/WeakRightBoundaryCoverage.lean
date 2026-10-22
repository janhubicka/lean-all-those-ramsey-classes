import AllThoseRamseyClasses.Lifts.GlobalRightComponentDirectPartnerFlip
import AllThoseRamseyClasses.Lifts.WeakRightBoundarySeparation

/-!
# Source-side boundary coverage for the arbitrary-width B-component flip

Let S be the complete common-root preimage of a weak EHN map into
a true full native functional free amalgam, and let B be the actual
right-exclusive Source minus S component containing x. Define
T=Cl(N(B)) ⊆ S. Even when T has arbitrarily many vertices:

* B remains EXACTLY the component of x after deleting T;
* every LEFT-exclusive source vertex a lies outside that component,
  and is therefore separated from x by T.

Thus the existence of a LEFT-side boundary partner is equivalent
to one remaining geometric INCLUSION: the generated external
neighborhood closure of the a-component after deleting T
must COVER every vertex of T. The opposite inclusion is automatic
because T is function-closed.

This is a much sharper geometric obstruction than an opaque
"partner exists" premise. It does not claim that coverage follows
from maximal-lift agreement, mixed-piece minimality, regularity, or
forbidden image closure. Under coverage and injectivity of f ON T,
the already verified direct arbitrary-width flip applies WITHOUT
any outer mixed piece and strictly decreases source right support.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F W U : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L W} {Source : Structure L U}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- If the generated boundary of the opposite LEFT component
covers T, it is automatically EQUAL to T: the reverse inclusion
comes from the closedness of T, not an additional premise.

This produces exactly the actual boundary partner needed for the
source-attached arbitrary-width flip; no singleton condition. -/
theorem weakRightComponent_oppositeCoverage_hasPartner
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W)
    (hf : Source.IsEHNHomomorphismEmbedding Whole f)
    (x : {z : U // z ∉
      weakFreeRootPart (sL := sL) (iL := iL) f})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := sL) (iL := iL) (iR := iR) f)
    (T : Set U)
    (hT : T = Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph
          (weakFreeRootPart (sL := sL) (iL := iL) f) x)))
    (hTS : T ⊆ weakFreeRootPart (sL := sL) (iL := iL) f)
    (a : U)
    (haLeft : a ∈ weakFreeLeftPart (sL := sL) (iL := iL) f)
    (hCoverage : ∀ y : {z : U // z ∉ T}, y.1 = a →
      T ⊆ Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph T y))) :
    ∃ y : {z : U // z ∉ T},
      y.1 = a ∧
      ¬ ReachOutside Source.graph T (outsideCutMap hTS x) y ∧
      Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph T y)) = T := by
  obtain ⟨y, hYa, hSep⟩ :=
    weakRightComponent_leftVertex_separatedByBoundary
      hFree f hf x hxRight T hT hTS a haLeft
  have hTclosed : Source.IsClosed T := by
    rw [hT]
    exact Source.functionClosure_isClosed
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph
          (weakFreeRootPart (sL := sL) (iL := iL) f) x))
  have hBoundLe : Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph T y)) ⊆ T :=
    functionalClosure_neighborhood_subset_cut
      Source T hTclosed y
  have hBoundary : Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph T y)) = T :=
    Set.Subset.antisymm hBoundLe (hCoverage y hYa)
  exact ⟨y, hYa, hSep, hBoundary⟩


/-- The EXACT remaining source-geometric coverage inclusion of an
opposite left-exclusive component, plus injectivity only on the
generated right-component boundary, is sufficient for a direct
arbitrary-width right-to-left source flip. No chosen outer mixed
piece and no arbitrary extra partner selection. -/
theorem rightComponent_oppositeCoverage_strictRightSupport
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
    (a : V)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (hCoverage : ∀ y : {z : V // z ∉ T}, y.1 = a →
      T ⊆ Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph T y)))
    (hConnected : ReachOutside Source.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨a, by simp⟩ : {z : V // z ∉ ∅}))
    (hInjT : Set.InjOn f T) :
    ∃ (V' : Type) (New : Structure L V'),
      F New ∧
      ∃ flip : V' → UT,
        New.IsEHNHomomorphismEmbedding Target flip ∧
        Nat.card {v : V' //
          flip v ∈ fullFreeRightExclusiveTarget iRight jRight} <
        Nat.card {v : V //
          f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  obtain ⟨y, hYa, hSep, hPartner⟩ :=
    weakRightComponent_oppositeCoverage_hasPartner
      hFree f hf x hxRight T hT hTS a haLeft hCoverage
  have hPathY : ReachOutside Source.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : V // z ∉ ∅}) := by
    simpa only [hYa] using hConnected
  exact rightComponent_partner_strictRightSupport
    F hFiniteF Source hFinite hForbidden
    Target f hf Left Right jLeft jRight X iLeft iRight
    hFree hCommon x hxRight
    T hT hTS y hSep hPartner hPathY hInjT

/-- In a RIGHT-support-minimal forbidden weak EHN witness, if a
left-exclusive component covers the complete generated boundary
of a right-exclusive S-component, then the target weak map must
collapse two distinct boundary vertices. The same boundary cannot
be pairwise covered by irreducible FULL source tests. -/
theorem minimalRightWitness_oppositeCoverage_forcesCollision
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
    (hTS : T ⊆ weakFreeRootPart
      (sL := iLeft) (iL := jLeft) w.toTarget)
    (a : w.Carrier)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) w.toTarget)
    (hCoverage : ∀ y : {z : w.Carrier // z ∉ T}, y.1 = a →
      T ⊆ w.source.functionClosure
        (gaifmanNeighborhood w.source.graph
          (componentFrom w.source.graph T y))) :
    (∃ u v : w.Carrier,
      u ∈ T ∧ v ∈ T ∧ u ≠ v ∧ w.toTarget u = w.toTarget v) ∧
      ¬ RootPairsCoveredByIrreducibleTests w.source T := by
  obtain ⟨y, _hYa, hSep, hPartner⟩ :=
    weakRightComponent_oppositeCoverage_hasPartner
      hFree w.toTarget w.homEmbedding
      x hxRight T hT hTS a haLeft hCoverage
  exact minimalRightWitness_partner_forcesBoundaryCollision
    F hFiniteF hConnected
    Target Left Right jLeft jRight
    X iLeft iRight hFree hCommon
    w hMinRight x hxRight T hT hTS y hSep hPartner

end AllThoseRamseyClasses.Lifts
