import AllThoseRamseyClasses.Lifts.Claim2ActualOneStepExteriorProfile
import AllThoseRamseyClasses.Lifts.Claim2NoEscapeFullAmalgamTransfer

/-!
# Track C: same-witness flip retains closedness, profile, support and no escape

The verified original global canonical B→A flip inside an actual
outer geometric piece P with its root in the full target seam
constructs ONE genuine new forbidden source New and weak EHN map.

The merged same-witness theorem already certifies the new
transported contextual vertex set K is closed, the complete
outer rooted all-test forbidden profile and ordered root target
coordinates are preserved, the B-exclusive SOURCE count inside
K drops strictly, and the A-exclusive SOURCE count outside K
is exactly unchanged.

The generic full-native free-amalgam no-escape transfer (stacked
parent) supplies the additional missing *geometric locality*
invariant: every Gaifman edge from a new contextual vertex
OUTSIDE the new target-root preimage stays inside the new K.

This needs no assumption that K is already a new genuine
minimal closed-separator piece. Thus one concrete B→A flip
preserves the full alternative **closed/no-escape** state
invariants for which a new B-source component and complete
generated boundary can be located inside K.

Still open: make the next B-only flip admissible for this
non-geometric K, and recover a genuinely selected outer piece
(or another eligible selected representative) for the terminal
original canonical A→B flip. No intermediate A-minimality,
global weak-image injectivity or frozen manuscript edits.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- ONE actual native B→A forbidden-source replacement preserves
the complete outer all-test rooted profile, ordered target roots,
exact exterior A-source count and no-escape geometric locality,
while strictly decreasing the interior B-source rank.

The old outer geometric root is explicitly required to lie in
the shared target seam. The new context need NOT be geometric
minimal-separator data; it is a function-closed no-escape set. -/
theorem geometricGlobalRightFlip_outerContextProfile_exteriorSupport_noEscape
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Forbidden n)
    (d : GeometricFunctionalPieceData Forbidden m)
    (hm : 0 < m)
    (hInnerInside :
      geometricPieceVertices Forbidden d ⊆
        geometricPieceVertices Forbidden P)
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hOuterRootInSeam : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hInnerRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hInnerNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hInnerRootInjective : Function.Injective
      (fun i : Fin m => f (d.roots i)))
    (oldVertex : V)
    (hvComponent : oldVertex ∈
      functionalComponentFrom Forbidden (Set.range d.roots) d.left)
    (hvRight : oldVertex ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f) :
    ∃ (V' : Type) (New : Structure L V'), F New ∧
      ∃ (Q : FunctionalRootExtension
          (geometricGlobalFunctionalChart Forbidden d).root)
        (iQ : Structure.Embedding Q.str New)
        (iE : Structure.Embedding
          (geometricGlobalComplementChart Forbidden d).str New),
        Structure.IsFreeAmalgam Q.rootEmbedding
          (geometricGlobalComplementChart Forbidden d).rootEmbedding iQ iE ∧
        ∃ (flip : V' → UT),
          New.IsEHNHomomorphismEmbedding Target flip ∧
          (∀ b : (geometricGlobalComplementChart Forbidden d).Carrier,
            flip (iE b) = f b.1) ∧
          ∃ (hNewK : New.IsClosed
              (iQ '' (Set.univ : Set Q.Carrier) ∪
                iE '' (oldOuterContextInInnerComplement Forbidden P d)))
            (newRoot : Structure.Embedding
              (geometricGlobalFunctionalChart Forbidden P).root
              (New.induce
                (iQ '' (Set.univ : Set Q.Carrier) ∪
                  iE '' (oldOuterContextInInnerComplement Forbidden P d))
                hNewK)),
            (functionalDiagramPieceSetoid
                (geometricGlobalFunctionalChart Forbidden P).root F).r
              (geometricGlobalFunctionalChart Forbidden P).ext
              ({ Carrier := {w : V' //
                    w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪
                      iE '' (oldOuterContextInInnerComplement Forbidden P d))},
                 str := New.induce
                  (iQ '' (Set.univ : Set Q.Carrier) ∪
                    iE '' (oldOuterContextInInnerComplement Forbidden P d))
                  hNewK,
                 rootEmbedding := newRoot } :
                FunctionalRootExtension
                  (geometricGlobalFunctionalChart Forbidden P).root) ∧
            (∀ i : Fin n,
              (newRoot i).1 =
                iE (⟨P.roots i, hOuterRootOutside i⟩ :
                  (geometricGlobalComplementChart Forbidden d).Carrier) ∧
              flip ((newRoot i).1) = f (P.roots i)) ∧
            Nat.card {w : V' //
              w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪
                iE '' (oldOuterContextInInnerComplement Forbidden P d)) ∧
              flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
            Nat.card {v : V //
              v ∈ geometricPieceVertices Forbidden P ∧
              f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
            Nat.card {w : V' //
              w ∉ (iQ '' (Set.univ : Set Q.Carrier) ∪
                iE '' (oldOuterContextInInnerComplement Forbidden P d)) ∧
              flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
            Nat.card {v : V //
              v ∉ geometricPieceVertices Forbidden P ∧
              f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ∧
            FunctionalContextNoEscapeOutsideSeam New
              (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip)
              (iQ '' (Set.univ : Set Q.Carrier) ∪
                iE '' (oldOuterContextInInnerComplement Forbidden P d)) := by
  classical
  obtain ⟨V', New, hNew, Q, iQ, iE, hNewFree,
      flip, hFlip, hSameComplement, hNewK, newRoot,
      hProfile, hRootCoordinates, hStrictB, hOutsideA⟩ :=
    geometricGlobalRightFlip_outerContextProfile_strictLocalExteriorSupport
      F hFiniteF Forbidden hFinite hForbidden
      P d hm hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootInjective
      oldVertex hvComponent hvRight
  let Inner := (geometricGlobalFunctionalChart Forbidden d).ext
  let E := geometricGlobalComplementChart Forbidden d
  let iOldInner : Structure.Embedding Inner.str Forbidden :=
    functionalComponentEmbedding Forbidden
      (Set.range d.roots) d.minimal.1 d.left
  let iOldE : Structure.Embedding E.str Forbidden :=
    functionalComponentComplementEmbedding Forbidden
      (Set.range d.roots) d.minimal.1 d.left
  have hOldFree :
      Structure.IsFreeAmalgam Inner.rootEmbedding
        E.rootEmbedding iOldInner iOldE :=
    geometricGlobalSource_freeDiagram Forbidden d
  let SOld : Set V :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) f
  let SNew : Set V' :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) flip
  let SR : Set E.Carrier :=
    oldOuterContextInInnerComplement Forbidden P d
  have hNewInnerRootInSeam :
      ∀ r : Fin m, iE (E.rootEmbedding r) ∈ SNew := by
    intro r
    change flip (iE (E.rootEmbedding r)) ∈
      Set.range (jLeft.comp iLeft)
    rw [hSameComplement (E.rootEmbedding r)]
    change f (d.roots r) ∈ Set.range (jLeft.comp iLeft)
    exact hInnerRoots ⟨r, rfl⟩
  have hSeamAgreement : ∀ b : E.Carrier,
      iE b ∈ SNew ↔ iOldE b ∈ SOld := by
    intro b
    change flip (iE b) ∈ Set.range (jLeft.comp iLeft) ↔
      f b.1 ∈ Set.range (jLeft.comp iLeft)
    rw [hSameComplement b]
  have hOldContextCarrier :
      iOldInner '' (Set.univ : Set Inner.Carrier) ∪
        iOldE '' SR =
      geometricPieceVertices Forbidden P :=
    geometricInnerSubpiece_oldOuterContext_eq
      Forbidden P d hInnerInside
  have hOldNoEscape :
      FunctionalContextNoEscapeOutsideSeam Forbidden SOld
        (iOldInner '' (Set.univ : Set Inner.Carrier) ∪
          iOldE '' SR) := by
    rw [hOldContextCarrier]
    exact geometricPiece_noEscapeOutsideContainingSeam
      Forbidden P SOld hOuterRootInSeam
  have hNewNoEscape :
      FunctionalContextNoEscapeOutsideSeam New SNew
        (iQ '' (Set.univ : Set Q.Carrier) ∪ iE '' SR) :=
    fullFreeAmalgam_noEscape_preserved_under_innerReplacement
      hOldFree hNewFree SOld SNew SR
      hNewInnerRootInSeam hSeamAgreement hOldNoEscape
  exact ⟨V', New, hNew, Q, iQ, iE, hNewFree,
    flip, hFlip, hSameComplement, hNewK, newRoot,
    hProfile, hRootCoordinates, hStrictB, hOutsideA,
    hNewNoEscape⟩

end AllThoseRamseyClasses.Lifts
