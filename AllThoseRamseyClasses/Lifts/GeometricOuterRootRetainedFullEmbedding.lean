import AllThoseRamseyClasses.Lifts.GlobalFlipClosedOuterContext
import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram
import PartiteConstruction.Functional.WeakOperations

/-!
# The old geometric outer root FULLY embeds in the retained complement

Under a literal inner flip, suppose each vertex of the OLD OUTER
piece's distinct ordered root lies outside the selected inner
component. The old inner complementary side E then contains all
these roots. Moreover the old outer piece is function-closed, so
the retained closed context SR = E ∩ (outer piece) also contains them.

The outer root is more than a vertex tuple: it carries the entire
FULL functional root structure of the original geometric chart.
We factor its genuine full embedding into the original source
through the genuine full retained complement and again through
the full induced retained outer context, preserving each ordered
root coordinate exactly.

This is an unconditional native source-geometry bridge under
the explicit `outer roots avoid flipped component` hypothesis.
No weak EHN map is made injective; no nested-cut assumption is used.
It does NOT establish that the new transported outer context is a
minimal-separator geometric piece or has the same outer-root
generated boundary. Those are separate Track A obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- If all old outer-root vertices survive the FULL inner-component
complement, there is an exact FULL native functional embedding of
the old geometric outer root (on Fin n) into the retained closed
complement `E ∩ outerPiece`.  Its vertex map is exactly the ordered
original root tuple, not a weak-map image or a chosen isomorphism. -/
theorem geometricOuterRoot_embedsFully_in_retainedComplement
    {V : Type} (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Old
        (Set.range d.roots) d.left) :
    let E := geometricGlobalComplementChart Old d
    let SR := oldOuterContextInInnerComplement Old P d
    let hSR : E.str.IsClosed SR :=
      oldOuterContextInInnerComplement_isClosed Old P d
    ∃ rT : Structure.Embedding
        (geometricGlobalFunctionalChart Old P).root
        (E.str.induce SR hSR),
      ∀ i : Fin n, (rT i).1.1 = P.roots i := by
  classical
  let E := geometricGlobalComplementChart Old d
  let SR := oldOuterContextInInnerComplement Old P d
  have hSR : E.str.IsClosed SR :=
    oldOuterContextInInnerComplement_isClosed Old P d
  let ROuter := (geometricGlobalFunctionalChart Old P).root
  let outerCut : Set V := Set.range P.roots
  let cutEmbedding : Structure.Embedding
      (closedCutRoot Old outerCut P.minimal.1) Old :=
    Structure.inclusion Old outerCut P.minimal.1
  let rootToOld : Structure.Embedding ROuter Old :=
    cutEmbedding.comp (geometricGlobalRootEmbedding Old P)
  let oldE : Structure.Embedding E.str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range d.roots) d.minimal.1 d.left
  let f : Fin n → E.Carrier :=
    fun i => ⟨P.roots i, hOuterRootOutside i⟩
  have hf (i : Fin n) : rootToOld i = oldE (f i) := by
    rfl
  let rootToE : Structure.Embedding ROuter E.str :=
    rootToOld.factorWithMap oldE f hf
  have hRootVal (i : Fin n) : (rootToE i).1 = P.roots i := by
    rfl
  have hRetained (i : Fin n) : rootToE i ∈ SR := by
    change (rootToE i).1 ∈ geometricPieceVertices Old P
    rw [hRootVal]
    exact Or.inl ⟨i, rfl⟩
  let incSR : Structure.Embedding
      (E.str.induce SR hSR) E.str :=
    Structure.inclusion E.str SR hSR
  let g : Fin n → SR := fun i => ⟨rootToE i, hRetained i⟩
  have hg (i : Fin n) : rootToE i = incSR (g i) := rfl
  let rT : Structure.Embedding ROuter (E.str.induce SR hSR) :=
    rootToE.factorWithMap incSR g hg
  refine ⟨rT, ?_⟩
  intro i
  exact hRootVal i

end AllThoseRamseyClasses.Lifts
