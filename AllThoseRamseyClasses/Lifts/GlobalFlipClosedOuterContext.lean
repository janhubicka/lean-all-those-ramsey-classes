import AllThoseRamseyClasses.Lifts.FullFreeAmalgamClosedContextUnion
import AllThoseRamseyClasses.Lifts.FullComplementClosedOuterRoot
import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram

/-!
# Closed outer context under a genuine inner functional piece replacement

Consider two source-attached geometric pieces of an OLD functional
structure. The inner piece has exact minimal closed root U and
selected component D, while the outer piece has closed vertex set
P. Assume ALL of U belongs to P.

Replace the inner piece with an arbitrary genuine full functional
root extension Q over the unchanged old complement E, making a
REAL full free amalgam NEW = Q +_U E. Put
  E_P = {e in E | oldComplement(e) belongs to P}.
Then E_P is native function-closed: it is the full-embedding
preimage of the original entire closed outer piece. It contains
the complete inner root U because U is contained in P.

Consequently the transported outer CONTEXT
  (newQ-image of ALL Q) union (newE-image of E_P)
is function-closed in NEW by the checked closed-union theorem
for full native functional free amalgams.

This is one exact ingredient of preservation of an outer piece
through a B-to-A flip. It uses complete function-value fibres,
including nullary symbols. It DOES NOT assert that the new context
is connected, is itself a geometric minimal-separator piece, or
has unchanged complete incompatibility profile. These last
properties require an additional contextual-gluing argument.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The part of a genuine old outer piece remaining in the unchanged
full native complement of an inner piece. The restriction is a
PREIMAGE under an actual full functional embedding, never a weak
incidence image. -/
def oldOuterContextInInnerComplement
    {V : Type}
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m) :
    Set (geometricGlobalComplementChart Old d).Carrier :=
  (functionalComponentComplementEmbedding Old
    (Set.range d.roots) d.minimal.1 d.left) ⁻¹'
      geometricPieceVertices Old P

/-- The old outer context inside the complete inner complement is
still function-closed, for arbitrary native relation/function arities.
No inclusion of the inner root is needed for this first assertion. -/
theorem oldOuterContextInInnerComplement_isClosed
    {V : Type}
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m) :
    (geometricGlobalComplementChart Old d).str.IsClosed
      (oldOuterContextInInnerComplement Old P d) := by
  let E := geometricGlobalComplementChart Old d
  let oldE : Structure.Embedding E.str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range d.roots) d.minimal.1 d.left
  have hOldP : Old.IsClosed (geometricPieceVertices Old P) :=
    functionalComponentUnion_isClosed Old
      (Set.range P.roots) P.minimal.1 P.left
  exact functionalEmbedding_preimage_closed E.str Old oldE
    (geometricPieceVertices Old P) hOldP

/-- If the entire source-side inner separating root U lies in the
old outer piece P, then the whole root on the unchanged full
complement side lies in the restriction E_P. -/
theorem oldOuterContext_contains_innerRoot
    {V : Type}
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hInnerRoot : ∀ i : Fin m,
      d.roots i ∈ geometricPieceVertices Old P) :
    ∀ i : Fin m,
      (geometricGlobalComplementChart Old d).rootEmbedding i ∈
        oldOuterContextInInnerComplement Old P d := by
  intro i
  change
    (functionalComponentComplementEmbedding Old
      (Set.range d.roots) d.minimal.1 d.left)
        ((geometricGlobalComplementChart Old d).rootEmbedding i) ∈
          geometricPieceVertices Old P
  have hEq :
      (functionalComponentComplementEmbedding Old
        (Set.range d.roots) d.minimal.1 d.left)
          ((geometricGlobalComplementChart Old d).rootEmbedding i)
            = d.roots i := rfl
  rw [hEq]
  exact hInnerRoot i

/-- An ACTUAL native free-amalgam replacement of an inner source
piece preserves the function-closedness of the whole transported
outer context Q union the retained old outer vertices in E.

The theorem is independent of forbidden-family equivalence and
does not assume target-map injectivity. It is the functional
closedness certificate before checking genuine geometric-piece
minimality and preservation of the outer incompatibility profile. -/
theorem geometricOuterContext_closed_after_innerReplacement
    {V W : Type}
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hInnerRoot : ∀ i : Fin m,
      d.roots i ∈ geometricPieceVertices Old P)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old d).root)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old d).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old d).rootEmbedding iQ iE) :
    New.IsClosed
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old P d)) := by
  have hQclosed : Q.str.IsClosed (Set.univ : Set Q.Carrier) := by
    intro f xs hxs y hy
    trivial
  exact fullFreeAmalgam_closed_union_of_closed_sides
    hFree
    (Set.univ : Set Q.Carrier)
    (oldOuterContextInInnerComplement Old P d)
    hQclosed
    (oldOuterContextInInnerComplement_isClosed Old P d)
    (fun _ => Set.mem_univ _)
    (oldOuterContext_contains_innerRoot Old P d hInnerRoot)

/-- If the outer root lies entirely in the unchanged old
complement of the inner piece, its transported vertices also
belong to the new function-closed outer context. Thus the
closed context contains the COMPLETE root intended for the
eventual reconstituted outer geometric piece. -/
theorem geometricOuterRoot_mem_closedContext_after_innerReplacement
    {V W : Type}
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (New : Structure L W)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old d).str New)
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Old
        (Set.range d.roots) d.left) :
    ∀ i : Fin n,
      iE (⟨P.roots i, hOuterRootOutside i⟩ :
        (geometricGlobalComplementChart Old d).Carrier) ∈
        iE '' (oldOuterContextInInnerComplement Old P d) := by
  intro i
  refine ⟨⟨P.roots i, hOuterRootOutside i⟩, ?_, rfl⟩
  exact Or.inl ⟨i, rfl⟩

end AllThoseRamseyClasses.Lifts
