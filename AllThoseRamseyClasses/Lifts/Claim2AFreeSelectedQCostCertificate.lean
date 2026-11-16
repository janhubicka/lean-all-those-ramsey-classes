import AllThoseRamseyClasses.Lifts.Claim2SelectedQGlobalBSourceBudget
import AllThoseRamseyClasses.Lifts.Claim2SelectedQAactiveSourceCost
import AllThoseRamseyClasses.Lifts.Claim2GlobalLexSourceMinimizer
import Mathlib.Tactic

/-!
# Track B: remember the OLD A-free selected component and exact new Q A-cost

The merged selected-Q geometric state relation retains the actual
selected forbidden Q, full native Q+old-E free-amalgam diagram, exact
complement target-map agreement and strict source B-rank decrease,
but does NOT itself record whether the REMOVED OLD selected component
was A-free. One must not apply the Track C exact A-exclusive source
support formula to that unrestricted relation without this hypothesis.

This module defines a strictly stronger SAME-Q provenance relation
which stores the A-freeness of its *identical chosen inner source
piece*. The actual eligible-one-sided source flip proves this full
certificate, not an independently invented Q. Forgetting A-freeness
recovers the old relation; the stronger relation exposes the precise
new Q-private A-exclusive SOURCE support cost.

At an ORIGINAL globally lex-minimal (A,B)-SOURCE weak forbidden map,
any such B-decreasing genuine selected-Q replacement MUST introduce
private A-exclusive source support. Thus A-neutrality of every Q
cannot be presumed from original A-minimality; rather, it would
contradict lex-minimality unless a geometric obstruction interrupts
the descent. We do not assert arbitrary intermediate states remain
A-minimal or lex-minimal. Frozen 2019 TeX unchanged.
-/

namespace AllThoseRamseyClasses.Lifts
open StructuralRamsey
open StructuralRamsey.Structure
universe u
variable {L : Language.{u}}

/-- Full original source and literal native Q provenance, with the
missing certificate that the actual OLD inner selected component
was A-exclusive-free. This is stronger than a contract-only step
and stronger than bare selected-Q provenance; there is no second Q. -/
def claim2NativeAFreeSelectedQStep
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    {n : ℕ} (hn : 0 < n)
    (s t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n) : Prop :=
    claim2NativeGeometricStep F Target Left Right
      jLeft jRight X iLeft iRight hn s t ∧
    ∃ (m : ℕ) (inner : GeometricFunctionalPieceData s.source m),
      0 < m ∧
      geometricPieceVertices s.source inner ⊆
        geometricPieceVertices s.source s.outer ∧
      (∀ z : s.Carrier,
        z ∈ functionalComponentFrom s.source
          (Set.range inner.roots) inner.left →
        z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) s.f) ∧
      ∃ (Q : FunctionalRootExtension
          (geometricGlobalFunctionalChart s.source inner).root),
        (FunctionalRootExtension.toEnumeratedRootedPattern
            (geometricGlobalFunctionalChart s.source inner).root
            (Equiv.refl (Fin m)) Q) ∈
          forbiddenGeometricFunctionalPieces F m ∧
        ∃ (iQ : Structure.Embedding Q.str t.source)
          (iE : Structure.Embedding
            (geometricGlobalComplementChart s.source inner).str t.source),
          Structure.IsFreeAmalgam
            Q.rootEmbedding
            (geometricGlobalComplementChart s.source inner).rootEmbedding
            iQ iE ∧
          (∀ q : Q.Carrier,
            t.f (iQ q) ∉ fullFreeRightExclusiveTarget iRight jRight) ∧
          (∀ e : (geometricGlobalComplementChart s.source inner).Carrier,
            t.f (iE e) = s.f e.1) ∧
          (iQ '' (Set.univ : Set Q.Carrier) ∪
             iE '' (oldOuterContextInInnerComplement s.source
               s.outer inner)) =
            geometricPieceVertices t.source t.outer


/-- Erase ONLY the checked old A-free certificate, retaining the
same literal selected Q+E source free-amalgam and all state data. -/
theorem claim2NativeAFreeSelectedQStep.toSelectedQProvenance
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    {n : ℕ} (hn : 0 < n)
    (s t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (hStep : claim2NativeAFreeSelectedQStep F Target Left Right
      jLeft jRight X iLeft iRight hn s t) :
    claim2NativeSelectedQProvenanceStep F Target Left Right
      jLeft jRight X iLeft iRight hn s t := by
  rcases hStep with ⟨hState, m, inner, hm, hInside, _hNoA,
      Q, hSelected, iQ, iE, hNewFree, hNoB, hEAgree, hCarrier⟩
  exact ⟨hState, m, inner, hm, hInside,
    Q, hSelected, iQ, iE, hNewFree, hNoB, hEAgree, hCarrier⟩


theorem claim2Native_eligibleInner_hasAFreeSelectedQStep
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
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (s : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (inner : GeometricFunctionalPieceData s.source m)
    (hInnerInside : geometricPieceVertices s.source inner ⊆
        geometricPieceVertices s.source s.outer)
    (hOuterRootOutside : ∀ i : Fin n,
      s.outer.roots i ∉ functionalComponentFrom s.source
        (Set.range inner.roots) inner.left)
    (hInnerRoots : Set.range inner.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) s.f)
    (hInnerNoLeft : ∀ z : s.Carrier,
      z ∈ functionalComponentFrom s.source
        (Set.range inner.roots) inner.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) s.f)
    (hInnerRootTargetInjective :
      Function.Injective (fun i : Fin m => s.f (inner.roots i)))
    (x : s.Carrier)
    (hxComponent : x ∈ functionalComponentFrom s.source
      (Set.range inner.roots) inner.left)
    (hxRight : x ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) s.f) :
    ∃ t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n,
      claim2NativeAFreeSelectedQStep F Target Left Right
        jLeft jRight X iLeft iRight hn s t := by
  have hAnchorA : s.f s.anchor ∈
      fullFreeLeftExclusiveTarget iLeft jLeft :=
    (weakFreeLeftPart_iff_targetExclusive
      iLeft jLeft s.f s.anchor).mp s.anchorLeft
  obtain ⟨V', New, hNew, Q, hSelected, iQ, iE, hNewFree,
      hFiniteNew, flip, newOuter, hFlip, hQNoB, hEAgree,
      hCarrier, hCoords, hSymbol, hRank, hExterior,
      anew, haOuter, haSame, haNewA, hNewRootInj,
      hNewBoundaryInj⟩ :=
    geometricGlobalRightFlip_actualOuterPiece_withExteriorAnchorRootAndBoundaryInj
      F hFiniteF s.source s.finite s.forbidden
      s.outer inner hm hn hInnerInside hOuterRootOutside
      Target s.f s.hom Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hInnerRoots hInnerNoLeft hInnerRootTargetInjective
      x hxComponent hxRight
      s.anchor s.anchorInOuter hAnchorA
      s.outerRootTargetInj s.activeBoundaryInj
  have hNewSeam : Set.range newOuter.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) flip := by
    rintro _ ⟨i, rfl⟩
    change flip (newOuter.roots i) ∈ Set.range (jLeft.comp iLeft)
    rw [hCoords i]
    exact s.outerRootInSeam ⟨i, rfl⟩
  have hNewAnchorLeft :
      anew ∈ weakFreeLeftPart (sL := iLeft) (iL := jLeft) flip :=
    (weakFreeLeftPart_iff_targetExclusive
      iLeft jLeft flip anew).mpr haNewA
  have hNewNativeBoundaryInj :
      ∀ (y : {w : V' //
          w ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) flip}),
        y.1 ∈ geometricPieceVertices New newOuter →
        y.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) flip →
        Set.InjOn flip
          (New.functionClosure
            (gaifmanNeighborhood New.graph
              (componentFrom New.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip) y))) :=
    claim2_fullRightActiveBoundary_to_weakRightActiveBoundary
      New newOuter Target flip X Left Right jLeft jRight
      iLeft iRight hFree hNewBoundaryInj
  let t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n :=
    { Carrier := V'
      source := New
      finite := hFiniteNew
      forbidden := hNew
      outer := newOuter
      f := flip
      hom := hFlip
      outerRootInSeam := hNewSeam
      anchor := anew
      anchorInOuter := haOuter
      anchorLeft := hNewAnchorLeft
      outerRootTargetInj := hNewRootInj
      activeBoundaryInj := hNewNativeBoundaryInj }
  refine ⟨t, ?_⟩
  have hStateStep :
      claim2NativeGeometricStep F Target Left Right
        jLeft jRight X iLeft iRight hn s t := by
    change (∀ i : Fin n,
        flip (newOuter.roots i) = s.f (s.outer.roots i)) ∧
      geometricGlobalPieceSymbol F s.source s.finite
        s.forbidden s.outer hn =
        geometricGlobalPieceSymbol F New hFiniteNew hNew newOuter hn ∧
      Nat.card {w : V' //
        w ∈ geometricPieceVertices New newOuter ∧
        flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
          claim2NativeBSourceRank s ∧
      (∀ TargetSet : Set UT,
        Nat.card {w : V' //
          w ∉ geometricPieceVertices New newOuter ∧
          flip w ∈ TargetSet} =
        Nat.card {v : s.Carrier //
          v ∉ geometricPieceVertices s.source s.outer ∧
          s.f v ∈ TargetSet}) ∧
      flip anew = s.f s.anchor
    exact ⟨hCoords, hSymbol, hRank, hExterior, haSame⟩
  exact ⟨hStateStep, m, inner, hm, hInnerInside,
    hInnerNoLeft, Q, hSelected, iQ, iE, hNewFree,
    hQNoB, hEAgree, hCarrier⟩


/-- Exact A-exclusive SOURCE support accounting, tied to the very
same actual Q from the one-sided native provenance certificate:
  new total A-source = old total A-source + private Q-nonroot A-source.
Every term counts literal source vertices, not distinct weak images.
This theorem does NOT posit A-neutrality of the selected Q. -/
theorem claim2NativeAFreeSelectedQStep_exactACost
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    {n : ℕ} (hn : 0 < n)
    (s t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (hStep : claim2NativeAFreeSelectedQStep F Target Left Right
      jLeft jRight X iLeft iRight hn s t) :
    ∃ (m : ℕ) (inner : GeometricFunctionalPieceData s.source m)
      (Q : FunctionalRootExtension
        (geometricGlobalFunctionalChart s.source inner).root)
      (iQ : Structure.Embedding Q.str t.source),
      Nat.card {w : t.Carrier //
        t.f w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
      Nat.card {v : s.Carrier //
        s.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} +
      Nat.card {q : Q.Carrier //
        q ∉ Set.range Q.rootEmbedding ∧
        t.f (iQ q) ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
  rcases hStep with ⟨_hState, m, inner, _hm, _hInside,
      hInnerNoA, Q, _hSelected, iQ, iE, hFree, _hNoB,
      hEAgree, _hCarrier⟩
  have hOldNoA :
      ∀ z : s.Carrier,
        z ∈ functionalComponentFrom s.source
          (Set.range inner.roots) inner.left →
        s.f z ∉ fullFreeLeftExclusiveTarget iLeft jLeft := by
    intro z hz hzA
    exact hInnerNoA z hz
      ((weakFreeLeftPart_iff_targetExclusive
        iLeft jLeft s.f z).mpr hzA)
  refine ⟨m, inner, Q, iQ, ?_⟩
  exact geometricSelectedQ_AfreeOld_exact_Aactive_cost
    s.source inner Q t.source t.finite iQ iE hFree
    s.f t.f (fullFreeLeftExclusiveTarget iLeft jLeft)
    hOldNoA hEAgree

/-- A global original (A,B)-lex-minimal forbidden native EHN witness
CANNOT undergo an A-neutral strictly B-source-decreasing actual
one-sided selected-Q flip. Its literal Q-provenance must therefore
exhibit POSITIVE SOURCE cardinality of private Q-nonroot vertices
mapped A-exclusive. This is an exact mathematical price, not a
hypothesis that every canonical Q necessarily pays it.

The hAMin and hBMinAtA are the ORIGINAL witness's global
lexicographic SOURCE minima over all forbidden weak maps; no such
minimum is claimed for an intermediate successor. -/
theorem claim2NativeOriginalLexMin_AFreeSelectedQStep_positivePrivateACost
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    {n : ℕ} (hn : 0 < n)
    (s t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (hStep : claim2NativeAFreeSelectedQStep F Target Left Right
      jLeft jRight X iLeft iRight hn s t)
    (hGlobalAMin :
      ∀ {Z : Type} (Candidate : Structure L Z)
        (hCandidate : F Candidate) (g : Z → UT),
        Candidate.IsEHNHomomorphismEmbedding Target g →
        Nat.card {v : s.Carrier //
          s.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
        Nat.card {z : Z //
          g z ∈ fullFreeLeftExclusiveTarget iLeft jLeft})
    (hBMinAtA :
      ∀ {Z : Type} (Candidate : Structure L Z)
        (hCandidate : F Candidate) (g : Z → UT),
        Candidate.IsEHNHomomorphismEmbedding Target g →
        Nat.card {z : Z //
          g z ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
        Nat.card {v : s.Carrier //
          s.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} →
        Nat.card {v : s.Carrier //
          s.f v ∈ fullFreeRightExclusiveTarget iRight jRight} ≤
        Nat.card {z : Z //
          g z ∈ fullFreeRightExclusiveTarget iRight jRight}) :
    ∃ (m : ℕ) (inner : GeometricFunctionalPieceData s.source m)
      (Q : FunctionalRootExtension
        (geometricGlobalFunctionalChart s.source inner).root)
      (iQ : Structure.Embedding Q.str t.source),
      0 < Nat.card {q : Q.Carrier //
        q ∉ Set.range Q.rootEmbedding ∧
        t.f (iQ q) ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
  obtain ⟨m, inner, Q, iQ, hExactCost⟩ :=
    claim2NativeAFreeSelectedQStep_exactACost
      F Target Left Right jLeft jRight X iLeft iRight hn s t hStep
  have hGlobalBStrict :
      Nat.card {w : t.Carrier //
        t.f w ∈ fullFreeRightExclusiveTarget iRight jRight} <
      Nat.card {v : s.Carrier //
        s.f v ∈ fullFreeRightExclusiveTarget iRight jRight} :=
    claim2NativeSelectedQStep_strictGlobalBSourceCount
      F Target Left Right jLeft jRight X iLeft iRight
      hn s t
      (claim2NativeAFreeSelectedQStep.toSelectedQProvenance
        F Target Left Right jLeft jRight X iLeft iRight
        hn s t hStep)
  have hAStrict :
      Nat.card {v : s.Carrier //
        s.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} <
      Nat.card {w : t.Carrier //
        t.f w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} :=
    globalLexMin_strictB_forces_strictAIncrease
      F Target s.source s.f t.source t.forbidden t.f t.hom
      (fullFreeLeftExclusiveTarget iLeft jLeft)
      (fullFreeRightExclusiveTarget iRight jRight)
      hGlobalAMin hBMinAtA hGlobalBStrict
  refine ⟨m, inner, Q, iQ, ?_⟩
  omega

end AllThoseRamseyClasses.Lifts
