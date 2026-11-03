import AllThoseRamseyClasses.Lifts.GlobalFlipClosedOuterContext
import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram

/-!
# The original transported context is EXACTLY the original outer piece

Let the inner selected full source component D sit entirely inside
an old geometric outer piece P, with the full inner separating root
also inside P.  When the original forbidden source is written as
  Old = Inner +_U E
with Inner=U union D and E=Old\D, the nested context
  K_old = Inner union (E intersect P)
is then LITERALLY the same vertex subset as P.

This is NOT a graph approximation, an image of a weak target map,
or a generated closure enlargement. It is exact equality of source
vertex sets, including the whole old outer root. Consequently any
native induced full functional structure along K_old is the actual
old geometric outer-piece structure after rewriting the carrier.
No claim is made that a NEW substituted context is also a
minimal-cut geometric piece; that requires the separate opposite
generated-boundary argument of Track A.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- If both the inner root and its WHOLE chosen component are
inside the old outer geometric piece, then the exact old
functional context obtained from inner-piece plus retained
full complement has precisely the old outer piece's vertices.

The source embeddings are the ACTUAL geometric full-chart
inclusions, never weak EHN maps. -/
theorem geometricOldOuterContext_eq_outerPieceVertices
    {V : Type}
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hInnerRoot : ∀ i : Fin m,
      d.roots i ∈ geometricPieceVertices Old P)
    (hInnerComponent :
      functionalComponentFrom Old (Set.range d.roots) d.left ⊆
        geometricPieceVertices Old P) :
    let iInner : Structure.Embedding
        (geometricGlobalFunctionalChart Old d).ext.str Old :=
      functionalComponentEmbedding Old (Set.range d.roots)
        d.minimal.1 d.left
    let iComplement : Structure.Embedding
        (geometricGlobalComplementChart Old d).str Old :=
      functionalComponentComplementEmbedding Old
        (Set.range d.roots) d.minimal.1 d.left
    iInner '' (Set.univ : Set
      (geometricGlobalFunctionalChart Old d).ext.Carrier) ∪
      iComplement '' oldOuterContextInInnerComplement Old P d =
        geometricPieceVertices Old P := by
  let InnerSet : Set V :=
    functionalComponentUnion Old (Set.range d.roots) d.left
  have hInnerSubset : InnerSet ⊆ geometricPieceVertices Old P := by
    intro v hv
    rcases hv with hRoot | hComp
    · obtain ⟨i, hi⟩ := hRoot
      rw [← hi]
      exact hInnerRoot i
    · exact hInnerComponent hComp
  apply Set.ext
  intro v
  constructor
  · rintro (⟨x, _hx, hv⟩ | ⟨y, hy, hv⟩)
    · rw [← hv]
      exact hInnerSubset x.2
    · rw [← hv]
      exact hy
  · intro hv
    by_cases hComp :
        v ∈ functionalComponentFrom Old (Set.range d.roots) d.left
    · exact Or.inl ⟨⟨v, Or.inr hComp⟩, Set.mem_univ _, rfl⟩
    · exact Or.inr ⟨⟨v, hComp⟩, hv, rfl⟩

end AllThoseRamseyClasses.Lifts
