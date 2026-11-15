import AllThoseRamseyClasses.Lifts.Claim2OriginalExtremalSelectedQCost
import AllThoseRamseyClasses.Lifts.Claim2WeakRightExclusiveTargetIff
import Mathlib.Data.Fintype.Card

/-!
# Track B/C: construct the initial full-native state from ONE smallest
          genuinely mixed geometric source piece

The original-extremal selected-Q theorem previously accepted an
existing full native geometric state s and a smallest mixed piece P
whose selected root, component and total piece vertex SETS matched.
This faithfully avoids a dependent width equality, but leaves the
initial state-package construction as an external obligation.

This module constructs THAT SAME native source state directly from
a genuinely mixed minimal-separator piece P of the SAME original
finite forbidden EHN weak witness: the A-exclusive anchor comes from
P.left_mixed, an actual B-exclusive SOURCE vertex from P.right_mixed
forces positive local B-source rank, and the full old root/active
boundary injection certificates remain explicit.

At an ORIGINAL globally A-source-support minimum and a smallest
mixed P, the verified all-width extremal source theorem then gives
one ACTUAL A-free SAME selected-Q native forbidden-source step
without independently assuming geometric root/component/piece
set equalities: they hold definitionally because s.outer=P.data.

This does NOT prove the missing INITIAL root/boundary injection,
nor existence of an initial mixed piece for arbitrary weak forbidden
maps, nor iterative preservation of original A-minimality.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Turn ONE genuine original mixed source-geometric piece into the
SAME native finite forbidden weak EHN state with a genuine A-source
anchor. The weak target map is not replaced or quotiented.
The ordered source root and B-active generated-boundary target
injections remain the exact original source premises. -/
noncomputable def claim2NativeGeometricState_ofMixedOriginalPiece
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (w : ForbiddenEHNWitness F Target)
    (P : MixedGeometricPiece w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget))
    (hRootInj : Function.Injective
      (fun i : Fin P.width => w.toTarget (P.data.roots i)))
    (hBoundaryInj :
      ∀ (x : {v : w.Carrier //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft)
            w.toTarget}),
        x.1 ∈ geometricPieceVertices w.source P.data →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft)
          (iR := jRight) w.toTarget →
        Set.InjOn w.toTarget
          (w.source.functionClosure
            (gaifmanNeighborhood w.source.graph
              (componentFrom w.source.graph
                (weakFreeRootPart
                  (sL := iLeft) (iL := jLeft) w.toTarget) x)))) :
    Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight P.width :=
  { Carrier := w.Carrier
    source := w.source
    finite := w.finiteCarrier
    forbidden := w.forbidden
    outer := P.data
    f := w.toTarget
    hom := w.homEmbedding
    outerRootInSeam := P.roots_in_common
    anchor := Classical.choose P.left_mixed
    anchorInOuter :=
      Or.inr (Classical.choose_spec P.left_mixed).1
    anchorLeft := (Classical.choose_spec P.left_mixed).2
    outerRootTargetInj := hRootInj
    activeBoundaryInj := hBoundaryInj }

/-- An ORIGINAL globally A-exclusive SOURCE-support-minimal
forbidden weak EHN witness containing a smallest actual mixed
geometric piece P of arbitrary POSITIVE root width, with its
ordered TARGET root and B-active generated boundary maps injected,
admits one actual forbidden A-free SAME selected Q B→A source
step on THAT SAME original witness. No silently chosen alternate
source/map, no image quotient, no dependent-width comparison.

The real A-anchor and positive B-source local rank come
directly from P.left_mixed and P.right_mixed. The two refined
smaller-root obstacles are excluded by the existing all-width
extremal theorem at this ORIGINAL state. -/
theorem claim2_originalAMinimal_smallestMixedPiece_hasActualAFreeQStep
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
    (hOriginalAMin : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft))
    (P : MixedGeometricPiece w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget))
    (hSmallest : ∀ Q : MixedGeometricPiece w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget),
      P.nonrootCount ≤ Q.nonrootCount)
    (hRootInj : Function.Injective
      (fun i : Fin P.width => w.toTarget (P.data.roots i)))
    (hBoundaryInj :
      ∀ (x : {v : w.Carrier //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft)
            w.toTarget}),
        x.1 ∈ geometricPieceVertices w.source P.data →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft)
          (iR := jRight) w.toTarget →
        Set.InjOn w.toTarget
          (w.source.functionClosure
            (gaifmanNeighborhood w.source.graph
              (componentFrom w.source.graph
                (weakFreeRootPart
                  (sL := iLeft) (iL := jLeft) w.toTarget) x)))) :
    ∃ t : Claim2NativeGeometricState F Target Left Right
        jLeft jRight X iLeft iRight P.width,
      claim2NativeAFreeSelectedQStep F Target Left Right
        jLeft jRight X iLeft iRight P.positive
        (claim2NativeGeometricState_ofMixedOriginalPiece
          F Target Left Right jLeft jRight X iLeft iRight
          w P hRootInj hBoundaryInj) t := by
  classical
  letI : Finite w.Carrier := w.finiteCarrier
  let s : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight P.width :=
    claim2NativeGeometricState_ofMixedOriginalPiece
      F Target Left Right jLeft jRight X iLeft iRight
      w P hRootInj hBoundaryInj
  obtain ⟨b, hbInComponent, hbRight⟩ := P.right_mixed
  have hbTargetRight :
      w.toTarget b ∈ fullFreeRightExclusiveTarget iRight jRight :=
    (weakFreeRightPart_iff_fullFreeRightExclusiveTarget
      iLeft iRight jLeft jRight hFree w.toTarget b).mp hbRight
  have hPositive :
      0 < claim2NativeBSourceRank s := by
    letI : Fintype {v : w.Carrier //
        v ∈ geometricPieceVertices w.source P.data ∧
        w.toTarget v ∈ fullFreeRightExclusiveTarget iRight jRight} :=
      Fintype.ofFinite _
    have hNonempty : Nonempty {v : w.Carrier //
        v ∈ geometricPieceVertices w.source P.data ∧
        w.toTarget v ∈ fullFreeRightExclusiveTarget iRight jRight} :=
      ⟨⟨b, Or.inr hbInComponent, hbTargetRight⟩⟩
    change 0 < Nat.card {v : w.Carrier //
      v ∈ geometricPieceVertices w.source P.data ∧
      w.toTarget v ∈ fullFreeRightExclusiveTarget iRight jRight}
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_pos_iff.mpr hNonempty)
  have hGlobalAMin :
      ∀ {W : Type} (New : Structure L W) (hNew : F New)
        (g : W → UT),
        New.IsEHNHomomorphismEmbedding Target g →
        Nat.card {v : s.Carrier //
          s.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
        Nat.card {z : W //
          g z ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
    intro W New hNew g hg
    let candidate : ForbiddenEHNWitness F Target :=
      { Carrier := W
        finiteCarrier := hFiniteF New hNew
        source := New
        forbidden := hNew
        toTarget := g
        homEmbedding := hg }
    have hMin := hOriginalAMin candidate
    change Nat.card {v : w.Carrier //
        w.toTarget v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
      Nat.card {z : W //
        g z ∈ fullFreeLeftExclusiveTarget iLeft jLeft} at hMin
    exact hMin
  have hRootSetEq :
      Set.range s.outer.roots = Set.range P.data.roots := rfl
  have hComponentEq :
      functionalComponentFrom s.source
        (Set.range s.outer.roots) s.outer.left =
      functionalComponentFrom s.source
        (Set.range P.data.roots) P.data.left := rfl
  have hPieceVertexEq :
      geometricPieceVertices s.source s.outer =
        geometricPieceVertices s.source P.data := rfl
  exact claim2Native_originalExtremal_positiveRank_hasAFreeSelectedQStep
    F hFiniteF hConnected Target Left Right jLeft jRight
    X iLeft iRight hFree hCommon P.positive s P
    hRootSetEq hComponentEq hPieceVertexEq
    hSmallest hPositive hGlobalAMin

end AllThoseRamseyClasses.Lifts
