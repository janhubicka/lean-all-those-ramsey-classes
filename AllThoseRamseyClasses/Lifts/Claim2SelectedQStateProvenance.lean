import AllThoseRamseyClasses.Lifts.Claim2HeterogeneousNativeState
import AllThoseRamseyClasses.Lifts.Claim2SameWitnessGeometricStateStep

/-!
# Track B: retain a literal selected-Q native diagram in an actual state step

Earlier Claim 2 finite iteration uses a heterogeneous state relation
that records the COMPLETE native forbidden source and geometric outer
piece, the original selected global symbol, ordered target root,
exterior SOURCE multiplicities, A-anchor and strict B-exclusive
SOURCE-rank decrease. Its step relation does NOT itself remember
the selected Q+E free-amalgam diagram creating the new source.

This additive module supplies a strictly stronger step certificate:
the SAME newly constructed forbidden source is the literal
selected-Q native free amalgam of the old complementary source E
and a forbidden selected rooted Q over a genuine nested inner piece.
The inserted Q produces NO new B-exclusive target images, the
target map agrees on ALL retained E vertices, and the NEW outer
geometric carrier is exactly inserted Q plus retained old outer
context. No second Q, quotient of source images, weak seam injection
or fabricated replacement is allowed.

We prove existence of such an explicit selected-Q state step under
the EXACT eligible one-sided inner-piece conditions already used
by the verified full-invariant geometric flip. This does not imply
every positive-rank state has an eligible inner piece, does not
eliminate smaller-root capture/A-mixedness, and does not yet promote
the abstract arbitrary finite chain to a chain storing Q on each edge.
-/

namespace AllThoseRamseyClasses.Lifts
open StructuralRamsey
open StructuralRamsey.Structure
universe u
variable {L : Language.{u}}

/-- The exact native SAME-selected-Q provenance of an actual step.
The first conjunct retains all externally necessary Claim 2 state
invariants; the second stores the literal selected forbidden
replacement Q, full native Q+old-complement embeddings and free
diagram, target-map agreement on EVERY E source vertex, no new
B-exclusive Q image, and actual new outer geometric source carrier. -/
def claim2NativeSelectedQProvenanceStep
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

/-- Forget literal Q-provenance while retaining the exact verified
heterogeneous Claim 2 state transition (and all its invariants). -/
theorem claim2NativeSelectedQProvenanceStep.toStateStep
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
    (hSelected : claim2NativeSelectedQProvenanceStep F Target Left Right
      jLeft jRight X iLeft iRight hn s t) :
    claim2NativeGeometricStep F Target Left Right
      jLeft jRight X iLeft iRight hn s t :=
  hSelected.1

/-- Under the explicit genuine one-sided nested inner piece inputs,
the verified SAME selected-Q geometric flip gives ONE new native
forbidden source state with both original injectivity certificates
and strict rank descent AND its literal full Q+E selected diagram.

This is an ACTUAL constructed source, not an abstract existential
replacement or a second independently chosen Q. -/
theorem claim2Native_eligibleInner_hasSelectedQProvenanceStep
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
      claim2NativeSelectedQProvenanceStep F Target Left Right
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
      activeBoundaryInj := hNewBoundaryInj }
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
    Q, hSelected, iQ, iE, hNewFree,
    hQNoB, hEAgree, hCarrier⟩

end AllThoseRamseyClasses.Lifts
