import AllThoseRamseyClasses.Lifts.GeometricNestedActualContextCarrier
import AllThoseRamseyClasses.Lifts.SelectedReplacementCompleteComponentWitness

/-!
# The genuine globally selected Q restores the exact older context carrier

This is the source-side endpoint of the repaired 2019 Claim 2
nested-context geometry. For an actual original functional
forbidden source with two genuinely nested minimal-closed-separator
geometric pieces, take the SAME genuinely selected rooted
replacement Q represented by the original global piece relation
and a literal FULL native functional replacement source New.

By the independent genuine-selection theorem,
Q has ONE private vertex d whose component both generates
the complete inner functional root and contains every other
Q-private vertex. The root-avoiding re-rooting step is essential:
complete generated boundary and whole-side connectivity were
originally established with potentially different witnesses.

The verified native full-amalgam component arguments then
identify the transported old outer closed context *exactly*
with the transported complete old outer root plus ONE new
old-cut component containing this actual selected Q vertex.

No old exterior boundary/privacy hypothesis, no new older
minimal-separator existence hypothesis, no assumed outer
context equality, no relation-only/function-graph shortcut,
and no weak target-map injectivity is required for THIS
source-carrier identity.

The separate older-root minimality and opposite-boundary
reconstruction, complete ordered Fin root representation,
all-test canonical global piece symbol and terminating
source support descent are not conclusions of this theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V W : Type}

/-- With genuine canonical selected-Q membership, the entire
actual nested transported outer context is the full old root
plus ONE connected new old-cut component. No Q connectivity
or complete root-boundary premises remain in the theorem
signature: BOTH are derived from the same selected witness.

This statement concerns full native source embeddings, allowing
arbitrary-arity relations/functions and incomparable inner/outer
closed cuts. It does not identify vertices under a weak EHN map. -/
theorem nestedGeometric_selectedQ_outerContext_exactCarrier
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    (Old : Structure L V)
    {n m : ℕ}
    (inner : GeometricFunctionalPieceData Old n)
    (outer : GeometricFunctionalPieceData Old m)
    (hNested :
      componentFrom Old.graph (Set.range inner.roots) inner.left ⊆
        componentFrom Old.graph (Set.range outer.roots) outer.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        (geometricGlobalFunctionalChart Old inner).root
        (Equiv.refl (Fin n)) Q) ∈
          forbiddenGeometricFunctionalPieces F n)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE) :
    let Comp := geometricGlobalComplementChart Old inner
    let oldE : Structure.Embedding Comp.str Old :=
      functionalComponentComplementEmbedding Old
        (Set.range inner.roots) inner.minimal.1 inner.left
    let T : Set Comp.Carrier := oldE ⁻¹' Set.range outer.roots
    ∃ (dQ : {q : Q.Carrier // q ∉ Set.range Q.rootEmbedding})
      (xNew : {w : W // w ∉ iE '' T}),
      xNew.1 = iQ dQ.1 ∧
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' oldOuterContextInInnerComplement Old outer inner) =
        (iE '' T) ∪
          componentFrom New.graph (iE '' T) xNew := by
  obtain ⟨dQ, hQBoundary, hAllQ⟩ :=
    selectedReplacementPiece_completeComponentWitness
      F (geometricGlobalFunctionalChart Old inner).root
      Q hSelected
  obtain ⟨xNew, hxNew, hCarrier⟩ :=
    nestedGeometric_actualTransportContext_eq_outerComponent
      Old inner outer hNested
      Q New iQ iE hNewFree
      dQ hQBoundary hAllQ
  exact ⟨dQ, xNew, hxNew, hCarrier⟩

end AllThoseRamseyClasses.Lifts
