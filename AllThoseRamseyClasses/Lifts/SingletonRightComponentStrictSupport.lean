import AllThoseRamseyClasses.Lifts.WeakSingletonBoundaryPartner
import AllThoseRamseyClasses.Lifts.RightBoundaryPartnerPieceFactor
import AllThoseRamseyClasses.Lifts.GlobalRightToLeftStrictSupport
import AllThoseRamseyClasses.Lifts.ForbiddenWeakWitnessMinimization
import AllThoseRamseyClasses.Lifts.ConnectedForbiddenPositivePiece

/-!
# An entire singleton-boundary right source component flips without an outer mixed piece

The original Section 3 Claim 2 works inside a smallest mixed
geometric piece P and repeatedly flips proper right-only sub-pieces.
At SINGLETON generated boundary there is a shorter proof.

Given any right-exclusive connected component B of Source minus the
full preimage S of the shared root, with T=Cl(N(B)) of cardinality at
most one and a connected left-exclusive source vertex elsewhere:
* the already verified source theorem constructs the missing
  boundary partner AUTOMATICALLY;
* B is exactly the selected nonroot component of a genuine minimal
  closed-separator piece of the original forbidden source;
* the complete EHN map of that piece factors into Right;
* connectedness makes the root nonempty and width one makes its
  target images injective;
* the ORIGINAL global quotient-indexed common full lift constructs
  a NEW forbidden source with STRICTLY fewer right-exclusive SOURCE
  vertices.

No preselected outer mixed piece P is used, and hence there is no
outer-piece preservation or repeated-flip invariant to prove in
this special case. No source-image quotient or global weak-map
injectivity is assumed.

The companion theorem prohibits such a right-only component in
a witness minimizing RIGHT support. The left-support minimization
of printed Claim 1, higher-width boundaries and general Section 3
strong amalgamation remain open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every connected right-exclusive component with singleton
generated boundary can be eliminated by one genuine forbidden
source B-to-A replacement with strict reduction of ORIGINAL
right-exclusive SOURCE support. There is NO outer piece P. -/
theorem singletonRightComponent_strictSupport_of_connectedOpposite
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
    (hSingleton : ∀ u v : V, u ∈ T → v ∈ T → u = v)
    (a : V)
    (haLeft : a ∈ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hConnected : ReachOutside Source.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨a, by simp⟩ : {z : V // z ∉ ∅})) :
    ∃ (V' : Type) (New : Structure L V'),
      F New ∧
      ∃ flip : V' → UT,
        New.IsEHNHomomorphismEmbedding Target flip ∧
        Nat.card {v : V' //
          flip v ∈ fullFreeRightExclusiveTarget iRight jRight} <
        Nat.card {v : V //
          f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  letI : Finite V := hFinite
  obtain ⟨y, hYa, hSep, hYBoundary⟩ :=
    weakRightComponent_singletonBoundary_hasPartner
      hFree f hf x hxRight T hT hTS hSingleton a haLeft hConnected
  obtain ⟨n, d, hRoot, hRootS, hLeft, hRight, hComp,
      pRight, _hpRight, hMap⟩ :=
    weakRightComponent_boundaryPartner_hasGenuineFactor
      hFree f hf x hxRight T hT hTS y hSep hYBoundary
  have hPathY : ReachOutside Source.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : V // z ∉ ∅}) := by
    simpa only [hYa] using hConnected
  have hPathD : ReachOutside Source.graph (∅ : Set V)
      (⟨d.left.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨d.right.1, by simp⟩ : {z : V // z ∉ ∅}) := by
    simpa only [hLeft, hRight] using hPathY
  have hn : 0 < n :=
    geometricPiece_positiveWidth_of_emptyCut_path Source d hPathD
  have hRootImageInjective :
      Function.Injective (fun i : Fin n => f (d.roots i)) := by
    intro i j _hEq
    apply d.roots_injective
    apply hSingleton
    · rw [← hRoot]
      exact ⟨i, rfl⟩
    · rw [← hRoot]
      exact ⟨j, rfl⟩
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

/-- An actual right-support-minimal finite forbidden weak EHN
witness cannot have ANY right-exclusive S-component with at most
one generated boundary vertex, as soon as the source is connected
and the opposite exclusive region is nonempty.

In particular no mixed outer piece or B-only proper-subpiece
selection is needed at singleton width. -/
theorem minimalRightWitness_noSingletonRightComponent
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
    (hSingleton : ∀ u v : w.Carrier, u ∈ T → v ∈ T → u = v)
    (a : w.Carrier)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) w.toTarget) :
    False := by
  have hPath : ReachOutside w.source.graph (∅ : Set w.Carrier)
      (⟨x.1, by simp⟩ : {z : w.Carrier // z ∉ ∅})
      (⟨a, by simp⟩ : {z : w.Carrier // z ∉ ∅}) :=
    gaifmanPath_to_emptyCutReach w.source
      ((hConnected w.source w.finiteCarrier w.forbidden).2 x.1 a)
  obtain ⟨V', New, hNew, flip, hFlip, hDrop⟩ :=
    singletonRightComponent_strictSupport_of_connectedOpposite
      F hFiniteF w.source w.finiteCarrier w.forbidden
      Target w.toTarget w.homEmbedding
      Left Right jLeft jRight X iLeft iRight
      hFree hCommon x hxRight
      T hT hTS hSingleton a haLeft hPath
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
