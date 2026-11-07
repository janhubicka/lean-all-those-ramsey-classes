import AllThoseRamseyClasses.Lifts.NestedCanonicalSelectedOuterContextCarrier
import AllThoseRamseyClasses.Lifts.Claim2ActualOneStepContextualFlip

/-!
# Exact local B-source support rank on one ACTUAL new outer-cut component

The printed Claim 2 descent counts B-exclusive SOURCE vertices inside
an actual source-attached outer geometric piece, rather than an arbitrary
closed context or the number of target images.

The verified one-step Track C theorem decreases this count on the full
transported closed context Q ∪ (E∩P), for ONE concrete right-to-left flip.
Merged Track A geometry (#895) identifies that context, for a
GENUINELY SELECTED Q, with the exact old root plus ONE new outer-cut
Gaifman component containing the inserted Q-private vertex.

This theorem combines those facts without selecting another Q or
assuming the new component's generated boundary. It also derives
the required source component nesting from precisely the original
\`innerPiece ⊆ outerPiece\` and \`outerRoot avoids innerComponent\`
premises of the verified local-support flip.

It does NOT yet claim an actual new minimal separating *geometric*
piece or preservation of the global relation: the selected Q carrier
is connected, but both generated boundary equations and reorientation
must be applied as in the separate Track A global-symbol proof.

No weak image quotient or target injectivity assumption is added.
The frozen 2019 manuscript is unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V W UT : Type}

/-- A strict local B-only SOURCE rank drop on the selected-Q transported
context is the SAME strict drop on the ACTUAL new old-root component.

The returned xNew is genuinely the inserted selected Q-private vertex.
This is a source-level equality and rank conversion, not a claim that
the new component is already an inclusion-minimal geometric separator.
-/
theorem selectedNestedFlip_strictLocalRank_on_actualOuterComponent
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    (Old : Structure L V)
    {n m : ℕ}
    (outer : GeometricFunctionalPieceData Old n)
    (inner : GeometricFunctionalPieceData Old m)
    (hInnerInside :
      geometricPieceVertices Old inner ⊆
        geometricPieceVertices Old outer)
    (hOuterRootOutside : ∀ i : Fin n,
      outer.roots i ∉
        functionalComponentFrom Old (Set.range inner.roots) inner.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        (geometricGlobalFunctionalChart Old inner).root
        (Equiv.refl (Fin m)) Q) ∈
          forbiddenGeometricFunctionalPieces F m)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (f : V → UT) (flip : W → UT)
    (BOnly : Set UT)
    (hStrictContext :
      Nat.card {w : W //
        w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪
          iE '' (oldOuterContextInInnerComplement Old outer inner)) ∧
        flip w ∈ BOnly} <
      Nat.card {v : V //
        v ∈ geometricPieceVertices Old outer ∧
        f v ∈ BOnly}) :
    let Comp := geometricGlobalComplementChart Old inner
    let oldE : Structure.Embedding Comp.str Old :=
      functionalComponentComplementEmbedding Old
        (Set.range inner.roots) inner.minimal.1 inner.left
    let T : Set Comp.Carrier := oldE ⁻¹' Set.range outer.roots
    ∃ (dQ : {q : Q.Carrier // q ∉ Set.range Q.rootEmbedding})
      (xNew : {w : W // w ∉ iE '' T}),
      xNew.1 = iQ dQ.1 ∧
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old outer inner)) =
        (iE '' T) ∪
          componentFrom New.graph (iE '' T) xNew ∧
      Nat.card {w : W //
        w ∈ ((iE '' T) ∪
          componentFrom New.graph (iE '' T) xNew) ∧
        flip w ∈ BOnly} <
      Nat.card {v : V //
        v ∈ geometricPieceVertices Old outer ∧
        f v ∈ BOnly} := by
  let Comp := geometricGlobalComplementChart Old inner
  let oldE : Structure.Embedding Comp.str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range inner.roots) inner.minimal.1 inner.left
  let T : Set Comp.Carrier := oldE ⁻¹' Set.range outer.roots
  have hNested :
      componentFrom Old.graph
        (Set.range inner.roots) inner.left ⊆
      componentFrom Old.graph
        (Set.range outer.roots) outer.left := by
    intro v hv
    have hvInOuter :
        v ∈ geometricPieceVertices Old outer :=
      hInnerInside (Or.inr hv)
    rcases hvInOuter with hRoot | hComp
    · obtain ⟨i, hi⟩ := hRoot
      have hNo : v ∉ componentFrom Old.graph
          (Set.range inner.roots) inner.left := by
        simpa only [hi] using hOuterRootOutside i
      exact False.elim (hNo hv)
    · exact hComp
  obtain ⟨dQ, xNew, hxQ, hCarrier⟩ :=
    nestedGeometric_selectedQ_outerContext_exactCarrier
      F Old inner outer hNested
      Q hSelected New iQ iE hFree
  have hRank :
      Nat.card {w : W //
        w ∈ ((iE '' T) ∪
          componentFrom New.graph (iE '' T) xNew) ∧
        flip w ∈ BOnly} <
      Nat.card {v : V //
        v ∈ geometricPieceVertices Old outer ∧
        f v ∈ BOnly} := by
    simpa only [← hCarrier] using hStrictContext
  exact ⟨dQ, xNew, hxQ, hCarrier, hRank⟩

end AllThoseRamseyClasses.Lifts
