import AllThoseRamseyClasses.Lifts.Claim2PositiveRankNoEscapeComponent
import AllThoseRamseyClasses.Lifts.Claim2NoEscapeProperOneSidedSubpiece
import AllThoseRamseyClasses.Lifts.WeakSingletonBoundaryPartner
import AllThoseRamseyClasses.Lifts.ConnectedForbiddenPositivePiece

/-!
# Track C: positive B-rank gives an ACTUAL proper flippable piece in the singleton-boundary case

The alternative contextual Claim 2 state need not carry a genuine
OUTER minimal closed separator: a function-closed, no-escape K
suffices for component and boundary localization.

Let a finite CONNECTED forbidden source admit an actual weak EHN
map into a full native functional target amalgam. Assume:
* K is closed and no-escape relative to the full shared seam S;
* K contains a genuine A-exclusive SOURCE anchor a;
* the number of B-exclusive SOURCE vertices inside K is positive;
* every B-exclusive S-component starting in K has a NONEMPTY,
  SINGLETON full generated boundary T=Cl(N(B)).

From positive B-support, the checked generic selector constructs
an actual B-exclusive vertex x∈K\S and its ENTIRE monochromatic
S-component B⊆K with T⊆S∩K.

Source connectedness gives a true Gaifman path from x to a.
The already kernel-checked singleton-boundary theorem constructs
an ACTUAL opposite generated-boundary partner y for T. Because
T is singleton, the original weak EHN target map is trivially
injective ON T (global injectivity is NOT required).

The verified generic closed/no-escape partner theorem then
constructs a genuine POSITIVE-width source geometric piece d:
* its FULL vertex set is a PROPER subset of K, omitting a;
* its entire ordered root lies in S∩K and its target images are
  injective;
* its selected nonroot component is EXACTLY the B-only
  S-component and contains a B-exclusive source witness x.

Thus the existence of a selected genuine flippable INNER piece
is established under a transparent singleton-boundary property,
even when K itself is NOT geometric and the current forbidden
source is NOT A-support-minimal.

The subsequent actual B→A flip with strict B-rank decrease and
no-escape/exterior-A preservation is the separate general
context theorem PR #880. The singleton hypothesis is not
known to hold at arbitrary positive rank. Mixed smaller roots
and collisions are still the genuine general obstructions.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every positive-B-rank native contextual state with an A-only
anchor and singleton complete generated boundaries of its
right-exclusive S-components contains an actual positive-width
PROPER B-only geometric source piece with injective target
root coordinates.

The outer context K is only closed/no-escape, not assumed to
be a minimal closed-separator geometric piece. The source map
need not minimize A-only support or be globally injective. -/
theorem positiveRank_noEscape_singletonBoundary_hasProperFlippablePiece
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
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
    (K : Set V) (hKclosed : Source.IsClosed K)
    (hNoEscape : FunctionalContextNoEscapeOutsideSeam Source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) K)
    (a : V) (haK : a ∈ K)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (hPositiveB : 0 < Nat.card {v : V //
      v ∈ K ∧ f v ∈ fullFreeRightExclusiveTarget iRight jRight})
    (hSingletonBoundaries :
      ∀ (x : {v : V //
        v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ K →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        let T : Set V := Source.functionClosure
          (gaifmanNeighborhood Source.graph
            (componentFrom Source.graph
              (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x))
        T.Nonempty ∧ ∀ u v : V, u ∈ T → v ∈ T → u = v) :
    ∃ (m : ℕ) (d : GeometricFunctionalPieceData Source m),
      0 < m ∧
      geometricPieceVertices Source d ⊂ K ∧
      Set.range d.roots ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) f ∩ K ∧
      Function.Injective (fun i : Fin m => f (d.roots i)) ∧
      (∀ z : V,
        z ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left →
        z ∉ weakFreeLeftPart
          (sL := iLeft) (iL := jLeft) f) ∧
      ∃ v : V,
        v ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left ∧
        v ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f := by
  classical
  letI : Finite V := hFinite
  let S : Set V :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) f
  let AOnly : Set V :=
    weakFreeLeftPart (sL := iLeft) (iL := jLeft) f
  obtain ⟨x, T, hxK, hxRight, _hCompInside,
      hCompRight, hT, hTInside⟩ :=
    positiveLocalRightSupport_noEscape_hasInnerComponent
      Source hFinite Target f hf
      Left Right jLeft jRight X iLeft iRight
      hFree K hKclosed hNoEscape hPositiveB
  have hSclosed : Source.IsClosed S :=
    weakFreeRootPart_isClosed
      (sL := iLeft) (iL := jLeft) f hf.1
  have hTS : T ⊆ S := fun z hz => (hTInside hz).1
  have hTnonempty : T.Nonempty := by
    rw [hT]
    exact (hSingletonBoundaries x hxK hxRight).1
  have hSingleton : ∀ u v : V,
      u ∈ T → v ∈ T → u = v := by
    intro u v hu hv
    apply (hSingletonBoundaries x hxK hxRight).2 u v
    · simpa only [hT] using hu
    · simpa only [hT] using hv
  have hConnectedPath : ReachOutside Source.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {v : V // v ∉ ∅})
      (⟨a, by simp⟩ : {v : V // v ∉ ∅}) :=
    gaifmanPath_to_emptyCutReach Source
      ((hConnected Source hFinite hForbidden).2 x.1 a)
  obtain ⟨y, _hYa, hSep, hYBoundary⟩ :=
    weakRightComponent_singletonBoundary_hasPartner
      hFree f hf x hxRight T hT hTS
      hSingleton a haLeft hConnectedPath
  have hBNoA : ∀ z : V,
      z ∈ componentFrom Source.graph S x → z ∉ AOnly := by
    intro z hz hzA
    exact (Set.disjoint_left.mp
      (weakFreePartition_left_right_disjoint hFree f))
        hzA (hCompRight z hz)
  have hInjT : Set.InjOn f T := by
    intro u hu v hv _heq
    exact hSingleton u v hu hv
  obtain ⟨m, d, hm, _hRootT, hRootInside, hProper,
      hComponentEq, hNoA, hRootInjective⟩ :=
    functionalNoEscape_properOneSidedGeometricSubpiece_of_partner
      Source S K hSclosed hKclosed hNoEscape
      x hxK AOnly hBNoA a haK haLeft.2 haLeft
      T hT hTS hTnonempty y hSep hYBoundary
      f hInjT
  have hxD : x.1 ∈ functionalComponentFrom Source
      (Set.range d.roots) d.left := by
    change x.1 ∈ componentFrom Source.graph
      (Set.range d.roots) d.left
    rw [hComponentEq]
    exact componentFrom_root Source.graph S x
  exact ⟨m, d, hm, hProper, hRootInside, hRootInjective,
    hNoA, x.1, hxD, hxRight⟩

end AllThoseRamseyClasses.Lifts
