import AllThoseRamseyClasses.Lifts.Claim2SelectedOneStepContextualFlip
import AllThoseRamseyClasses.Lifts.NestedSelectedGeometricFullSourceInvariants
import AllThoseRamseyClasses.Lifts.CanonicalGlueDiagramBridge

/-!
# One REAL right-to-left Claim 2 flip with a new outer geometric piece

This joins the verified same-Q strictly decreasing local B-SOURCE
context flip (#922) to the strengthening of actual native geometric
outer piece/profile/symbol restoration (#927), with ONE actual
selected replacement Q, ONE full forbidden new source, and ONE
weak EHN map.

The new outer piece is a genuine minimal closed separator with the
ORIGINAL ordered entire outer root; its true global canonical
piece symbol equals the old one, and the B-only SOURCE vertex
rank inside the WHOLE new geometric piece strictly decreases.
The flip agrees with the old weak map on every old complement
vertex; target root coordinates are therefore unchanged.

Hypotheses are precisely those of the original concrete B-to-A
same-witness support theorem, plus positive old OUTER root width
for the global quotient symbol. Old inner-piece containment and
outer-root avoidance imply actual inner COMPONENT nesting; neither
inner/outer cut inclusion nor a weak-image quotient is assumed.

This module contains the stronger same-selected-Q step with exact
exterior SOURCE support conservation for arbitrary target subsets.
The original strict-local-rank theorem is its direct corollary,
eliminating the duplicate 2019 source-flip proof while retaining
the older public theorem signature. The refactor requires its
own exact-head CI/axiom checks.

The existence of a flippable inner piece at every positive rank,
the terminal A-minimizer contradiction and weak target-root
collisions remain separate Track C/D obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Concrete original Claim 2 right-to-left inner source flip:
one actual geometrically selected Q, one NEW forbidden full source,
one genuine outer geometric piece, and its original ordered ROOTED
functional all-test incompatibility profile. Also preserves the same
global piece symbol and every exterior SOURCE-support count while
strictly decreasing the interior B-exclusive SOURCE rank.

This stronger endpoint is the unique construction; the historical
withExterior API below is a direct corollary. It does not prove the
existence of a positive-rank flippable subpiece at every iteration or
the final A-minimality contradiction. -/
theorem geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport_withExteriorAndAllTests_withNoNewRight
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Old : Structure L V)
    (hFinite : Finite V) (hOld : F Old)
    {n m : ℕ}
    (outer : GeometricFunctionalPieceData Old n)
    (inner : GeometricFunctionalPieceData Old m)
    (hm : 0 < m) (hn : 0 < n)
    (hInnerInside :
      geometricPieceVertices Old inner ⊆
        geometricPieceVertices Old outer)
    (hOuterRootOutside : ∀ i : Fin n,
      outer.roots i ∉ functionalComponentFrom Old
        (Set.range inner.roots) inner.left)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Old.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hInnerRoots : Set.range inner.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hInnerNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hInnerRootInjective : Function.Injective
      (fun i : Fin m => f (inner.roots i)))
    (oldVertex : V)
    (hvComponent : oldVertex ∈
      functionalComponentFrom Old
        (Set.range inner.roots) inner.left)
    (hvRight : oldVertex ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f) :
    ∃ (V' : Type) (New : Structure L V') (hNew : F New)
      (Q : FunctionalRootExtension
        (geometricGlobalFunctionalChart Old inner).root)
      (hSelected :
        (FunctionalRootExtension.toEnumeratedRootedPattern
          (geometricGlobalFunctionalChart Old inner).root
          (Equiv.refl (Fin m)) Q) ∈
            forbiddenGeometricFunctionalPieces F m)
      (iQ : Structure.Embedding Q.str New)
      (iE : Structure.Embedding
        (geometricGlobalComplementChart Old inner).str New)
      (hNewFree : Structure.IsFreeAmalgam Q.rootEmbedding
        (geometricGlobalComplementChart Old inner).rootEmbedding
        iQ iE)
      (flip : V' → UT)
      (hFlip : New.IsEHNHomomorphismEmbedding Target flip)
      (hFiniteNew : Finite V')
      (newOuter : GeometricFunctionalPieceData New n)
      (hRoot : (geometricGlobalFunctionalChart Old outer).root =
        (geometricGlobalFunctionalChart New newOuter).root),
      (∀ q : Q.Carrier,
        flip (iQ q) ∉ fullFreeRightExclusiveTarget iRight jRight) ∧
      (∀ b : (geometricGlobalComplementChart Old inner).Carrier,
        flip (iE b) = f b.1) ∧
      (∀ i : Fin n,
        newOuter.roots i =
          iE (⟨outer.roots i, hOuterRootOutside i⟩ :
            (geometricGlobalComplementChart Old inner).Carrier)) ∧
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old outer inner)) =
          geometricPieceVertices New newOuter ∧
      (∀ i : Fin n,
        flip (newOuter.roots i) = f (outer.roots i)) ∧
      geometricGlobalPieceSymbol F Old
          hFinite hOld outer hn =
        geometricGlobalPieceSymbol F New
          hFiniteNew hNew newOuter hn ∧
      Nat.card {w : V' //
        w ∈ geometricPieceVertices New newOuter ∧
        flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
      Nat.card {v : V //
        v ∈ geometricPieceVertices Old outer ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
      (∀ TargetSet : Set UT,
        Nat.card {w : V' //
          w ∉ geometricPieceVertices New newOuter ∧
          flip w ∈ TargetSet} =
        Nat.card {v : V //
          v ∉ geometricPieceVertices Old outer ∧
          f v ∈ TargetSet})
      ∧ (functionalDiagramPieceSetoid
          (geometricGlobalFunctionalChart Old outer).root F).r
          (geometricGlobalFunctionalChart Old outer).ext
          (hRoot.symm ▸
            (geometricGlobalFunctionalChart New newOuter).ext) := by
  letI : Finite V := hFinite
  have hNested :
      componentFrom Old.graph
        (Set.range inner.roots) inner.left ⊆
      componentFrom Old.graph
        (Set.range outer.roots) outer.left := by
    intro v hv
    have hvOuter : v ∈ geometricPieceVertices Old outer :=
      hInnerInside (Or.inr hv)
    rcases hvOuter with hRoot | hComponent
    · obtain ⟨i, hi⟩ := hRoot
      have hNo : v ∉ componentFrom Old.graph
          (Set.range inner.roots) inner.left := by
        simpa only [hi] using hOuterRootOutside i
      exact False.elim (hNo hv)
    · exact hComponent
  obtain ⟨V', New, hNew, Q, hInnerProfile, hSelected,
    iQ, iE, hNewFree, flip, hFlip, hQNoRight, hEAgree,
    _hClosed, _hRootInjective, _hRootFixed, hStrictContext⟩ :=
    geometricGlobalRightFlip_outerContextClosed_strictLocalRightSupport_withInnerProfile_andComplementAgreement_selected_withNoNewRight
      F hFiniteF Old hFinite hOld
      outer inner hm hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootInjective
      oldVertex hvComponent hvRight
  have hDiagram :
      (functionalDiagramPieceSetoid
        (geometricGlobalFunctionalChart Old inner).root F).r
        (geometricGlobalFunctionalChart Old inner).ext Q :=
    (functionalDiagramPiece_equiv_iff_glue
      (geometricGlobalFunctionalChart Old inner).root
      F (geometricGlobalFunctionalChart Old inner).ext Q).mpr
      hInnerProfile
  obtain ⟨hFiniteNew, newOuter, hRoot, hRootCoords,
      hSymbol, hCarrier, hTargetCoords, hRank, hExterior,
      hProfile⟩ :=
    nestedGeometric_selectedFlip_fullSourceStepInvariants_withAllTests
      F Old hOld inner outer hNested Q hSelected hDiagram
      New hNew iQ iE hNewFree hn
      f flip hEAgree (fullFreeRightExclusiveTarget iRight jRight)
      hStrictContext
  have hRootCoordsOriginal : ∀ i : Fin n,
      newOuter.roots i =
        iE (⟨outer.roots i, hOuterRootOutside i⟩ :
          (geometricGlobalComplementChart Old inner).Carrier) := by
    intro i
    exact hRootCoords i
  exact ⟨V', New, hNew, Q, hSelected,
    iQ, iE, hNewFree, flip, hFlip,
    hFiniteNew, newOuter, hRoot, hQNoRight, hEAgree,
    hRootCoordsOriginal, hCarrier, hTargetCoords, hSymbol, hRank, hExterior,
    hProfile⟩

/-- Backwards-compatible all-tests selected-Q successor. The
stronger public theorem also certifies that this SAME replacement
Q has no B-exclusive SOURCE target images. Its original quotient
profile, source geometry and exterior-count conclusions are
retained here by projection, without repeating the flip proof. -/
theorem geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport_withExteriorAndAllTests
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Old : Structure L V)
    (hFinite : Finite V) (hOld : F Old)
    {n m : ℕ}
    (outer : GeometricFunctionalPieceData Old n)
    (inner : GeometricFunctionalPieceData Old m)
    (hm : 0 < m) (hn : 0 < n)
    (hInnerInside :
      geometricPieceVertices Old inner ⊆
        geometricPieceVertices Old outer)
    (hOuterRootOutside : ∀ i : Fin n,
      outer.roots i ∉ functionalComponentFrom Old
        (Set.range inner.roots) inner.left)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Old.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hInnerRoots : Set.range inner.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hInnerNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hInnerRootInjective : Function.Injective
      (fun i : Fin m => f (inner.roots i)))
    (oldVertex : V)
    (hvComponent : oldVertex ∈
      functionalComponentFrom Old
        (Set.range inner.roots) inner.left)
    (hvRight : oldVertex ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f) :
    ∃ (V' : Type) (New : Structure L V') (hNew : F New)
      (Q : FunctionalRootExtension
        (geometricGlobalFunctionalChart Old inner).root)
      (hSelected :
        (FunctionalRootExtension.toEnumeratedRootedPattern
          (geometricGlobalFunctionalChart Old inner).root
          (Equiv.refl (Fin m)) Q) ∈
            forbiddenGeometricFunctionalPieces F m)
      (iQ : Structure.Embedding Q.str New)
      (iE : Structure.Embedding
        (geometricGlobalComplementChart Old inner).str New)
      (hNewFree : Structure.IsFreeAmalgam Q.rootEmbedding
        (geometricGlobalComplementChart Old inner).rootEmbedding
        iQ iE)
      (flip : V' → UT)
      (hFlip : New.IsEHNHomomorphismEmbedding Target flip)
      (hFiniteNew : Finite V')
      (newOuter : GeometricFunctionalPieceData New n)
      (hRoot : (geometricGlobalFunctionalChart Old outer).root =
        (geometricGlobalFunctionalChart New newOuter).root),
      (∀ b : (geometricGlobalComplementChart Old inner).Carrier,
        flip (iE b) = f b.1) ∧
      (∀ i : Fin n,
        newOuter.roots i =
          iE (⟨outer.roots i, hOuterRootOutside i⟩ :
            (geometricGlobalComplementChart Old inner).Carrier)) ∧
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old outer inner)) =
          geometricPieceVertices New newOuter ∧
      (∀ i : Fin n,
        flip (newOuter.roots i) = f (outer.roots i)) ∧
      geometricGlobalPieceSymbol F Old
          hFinite hOld outer hn =
        geometricGlobalPieceSymbol F New
          hFiniteNew hNew newOuter hn ∧
      Nat.card {w : V' //
        w ∈ geometricPieceVertices New newOuter ∧
        flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
      Nat.card {v : V //
        v ∈ geometricPieceVertices Old outer ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
      (∀ TargetSet : Set UT,
        Nat.card {w : V' //
          w ∉ geometricPieceVertices New newOuter ∧
          flip w ∈ TargetSet} =
        Nat.card {v : V //
          v ∉ geometricPieceVertices Old outer ∧
          f v ∈ TargetSet})
      ∧ (functionalDiagramPieceSetoid
          (geometricGlobalFunctionalChart Old outer).root F).r
          (geometricGlobalFunctionalChart Old outer).ext
          (hRoot.symm ▸
            (geometricGlobalFunctionalChart New newOuter).ext) := by
  obtain ⟨V', New, hNew, Q, hSelected, iQ, iE,
      hNewFree, flip, hFlip, hFiniteNew, newOuter,
      hRoot, _hQNoRight, hEAgree, hRootCoords,
      hCarrier, hTargetCoords, hSymbol, hRank,
      hExterior, hProfile⟩ :=
    geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport_withExteriorAndAllTests_withNoNewRight
      F hFiniteF Old hFinite hOld
      outer inner hm hn hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootInjective
      oldVertex hvComponent hvRight
  exact ⟨V', New, hNew, Q, hSelected, iQ, iE,
    hNewFree, flip, hFlip, hFiniteNew, newOuter,
    hRoot, hEAgree, hRootCoords, hCarrier,
    hTargetCoords, hSymbol, hRank, hExterior, hProfile⟩

/-- The concrete same-selected-Q B-to-A flip with an ACTUAL
minimal-separator outer successor and exact exterior support
invariance for ALL target subsets, in addition to the strict
interior B-exclusive SOURCE count decrease. -/
theorem geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport_withExterior
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Old : Structure L V)
    (hFinite : Finite V) (hOld : F Old)
    {n m : ℕ}
    (outer : GeometricFunctionalPieceData Old n)
    (inner : GeometricFunctionalPieceData Old m)
    (hm : 0 < m) (hn : 0 < n)
    (hInnerInside :
      geometricPieceVertices Old inner ⊆
        geometricPieceVertices Old outer)
    (hOuterRootOutside : ∀ i : Fin n,
      outer.roots i ∉ functionalComponentFrom Old
        (Set.range inner.roots) inner.left)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Old.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hInnerRoots : Set.range inner.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hInnerNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hInnerRootInjective : Function.Injective
      (fun i : Fin m => f (inner.roots i)))
    (oldVertex : V)
    (hvComponent : oldVertex ∈
      functionalComponentFrom Old
        (Set.range inner.roots) inner.left)
    (hvRight : oldVertex ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f) :
    ∃ (V' : Type) (New : Structure L V') (hNew : F New)
      (Q : FunctionalRootExtension
        (geometricGlobalFunctionalChart Old inner).root)
      (hSelected :
        (FunctionalRootExtension.toEnumeratedRootedPattern
          (geometricGlobalFunctionalChart Old inner).root
          (Equiv.refl (Fin m)) Q) ∈
            forbiddenGeometricFunctionalPieces F m)
      (iQ : Structure.Embedding Q.str New)
      (iE : Structure.Embedding
        (geometricGlobalComplementChart Old inner).str New)
      (hNewFree : Structure.IsFreeAmalgam Q.rootEmbedding
        (geometricGlobalComplementChart Old inner).rootEmbedding
        iQ iE)
      (flip : V' → UT)
      (hFlip : New.IsEHNHomomorphismEmbedding Target flip)
      (hFiniteNew : Finite V')
      (newOuter : GeometricFunctionalPieceData New n),
      (∀ b : (geometricGlobalComplementChart Old inner).Carrier,
        flip (iE b) = f b.1) ∧
      (∀ i : Fin n,
        newOuter.roots i =
          iE (⟨outer.roots i, hOuterRootOutside i⟩ :
            (geometricGlobalComplementChart Old inner).Carrier)) ∧
      (∀ i : Fin n,
        flip (newOuter.roots i) = f (outer.roots i)) ∧
      geometricGlobalPieceSymbol F Old
          hFinite hOld outer hn =
        geometricGlobalPieceSymbol F New
          hFiniteNew hNew newOuter hn ∧
      Nat.card {w : V' //
        w ∈ geometricPieceVertices New newOuter ∧
        flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
      Nat.card {v : V //
        v ∈ geometricPieceVertices Old outer ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} ∧
      (∀ TargetSet : Set UT,
        Nat.card {w : V' //
          w ∉ geometricPieceVertices New newOuter ∧
          flip w ∈ TargetSet} =
        Nat.card {v : V //
          v ∉ geometricPieceVertices Old outer ∧
          f v ∈ TargetSet}) := by
  obtain ⟨V', New, hNew, Q, hSelected, iQ, iE, hNewFree,
      flip, hFlip, hFiniteNew, newOuter, _hRoot, hEAgree,
      hRootCoords, _hCarrier, hTargetCoords, hSymbol, hRank, hExterior,
      _hProfile⟩ :=
    geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport_withExteriorAndAllTests
      F hFiniteF Old hFinite hOld outer inner hm hn
      hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootInjective
      oldVertex hvComponent hvRight
  exact ⟨V', New, hNew, Q, hSelected, iQ, iE, hNewFree,
    flip, hFlip, hFiniteNew, newOuter, hEAgree, hRootCoords,
    hTargetCoords, hSymbol, hRank, hExterior⟩

/-- A single actual selected B-to-A right source flip simultaneously
returns: genuine selected Q, literal full native forbidden diagram,
unchanged entire old complement weak map, a genuine old-rooted
new geometric outer piece with its SAME GLOBAL piece symbol,
unchanged old outer target root coordinates, and strictly fewer
B-exclusive SOURCE vertices inside that actual geometric piece.

No hidden independent existential Q is introduced and no arbitrary
weak EHN target map is assumed to be globally injective. -/
theorem geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Old : Structure L V)
    (hFinite : Finite V) (hOld : F Old)
    {n m : ℕ}
    (outer : GeometricFunctionalPieceData Old n)
    (inner : GeometricFunctionalPieceData Old m)
    (hm : 0 < m) (hn : 0 < n)
    (hInnerInside :
      geometricPieceVertices Old inner ⊆
        geometricPieceVertices Old outer)
    (hOuterRootOutside : ∀ i : Fin n,
      outer.roots i ∉ functionalComponentFrom Old
        (Set.range inner.roots) inner.left)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Old.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hInnerRoots : Set.range inner.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hInnerNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hInnerRootInjective : Function.Injective
      (fun i : Fin m => f (inner.roots i)))
    (oldVertex : V)
    (hvComponent : oldVertex ∈
      functionalComponentFrom Old
        (Set.range inner.roots) inner.left)
    (hvRight : oldVertex ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f) :
    ∃ (V' : Type) (New : Structure L V') (hNew : F New)
      (Q : FunctionalRootExtension
        (geometricGlobalFunctionalChart Old inner).root)
      (hSelected :
        (FunctionalRootExtension.toEnumeratedRootedPattern
          (geometricGlobalFunctionalChart Old inner).root
          (Equiv.refl (Fin m)) Q) ∈
            forbiddenGeometricFunctionalPieces F m)
      (iQ : Structure.Embedding Q.str New)
      (iE : Structure.Embedding
        (geometricGlobalComplementChart Old inner).str New)
      (hNewFree : Structure.IsFreeAmalgam Q.rootEmbedding
        (geometricGlobalComplementChart Old inner).rootEmbedding
        iQ iE)
      (flip : V' → UT)
      (hFlip : New.IsEHNHomomorphismEmbedding Target flip)
      (hFiniteNew : Finite V')
      (newOuter : GeometricFunctionalPieceData New n),
      (∀ b : (geometricGlobalComplementChart Old inner).Carrier,
        flip (iE b) = f b.1) ∧
      (∀ i : Fin n,
        newOuter.roots i =
          iE (⟨outer.roots i, hOuterRootOutside i⟩ :
            (geometricGlobalComplementChart Old inner).Carrier)) ∧
      (∀ i : Fin n,
        flip (newOuter.roots i) = f (outer.roots i)) ∧
      geometricGlobalPieceSymbol F Old
          hFinite hOld outer hn =
        geometricGlobalPieceSymbol F New
          hFiniteNew hNew newOuter hn ∧
      Nat.card {w : V' //
        w ∈ geometricPieceVertices New newOuter ∧
        flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
      Nat.card {v : V //
        v ∈ geometricPieceVertices Old outer ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  obtain ⟨V', New, hNew, Q, hSelected, iQ, iE, hNewFree,
      flip, hFlip, hFiniteNew, newOuter, hEAgree, hRootCoords,
      hTargetCoords, hSymbol, hRank, _hExterior⟩ :=
    geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport_withExterior
      F hFiniteF Old hFinite hOld outer inner hm hn
      hInnerInside hOuterRootOutside
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootInjective
      oldVertex hvComponent hvRight
  exact ⟨V', New, hNew, Q, hSelected, iQ, iE, hNewFree,
    flip, hFlip, hFiniteNew, newOuter, hEAgree, hRootCoords,
    hTargetCoords, hSymbol, hRank⟩

end AllThoseRamseyClasses.Lifts
