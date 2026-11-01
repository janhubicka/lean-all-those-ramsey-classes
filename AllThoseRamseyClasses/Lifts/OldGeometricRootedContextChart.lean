import AllThoseRamseyClasses.Lifts.GeometricOuterRootRetainedFullEmbedding
import AllThoseRamseyClasses.Lifts.OldOuterGeometricContextExactCarrier
import AllThoseRamseyClasses.Lifts.NamedNestedFunctionalContext

/-!
# Exact old outer-piece chart from the retained native source context

For a proper inner piece inside a geometric old outer piece, with
its WHOLE component and whole separating root inside the old piece,
and with the old outer-root tuple entirely outside the flipped inner
component, the old nested context is not merely abstractly equivalent
to the original outer piece: it is the exact same set of source vertices.

This theorem constructs a full rooted functional embedding from
the ORIGINAL ordered outer root structure into the actual old
induced context, and checks its exact source coordinates. It pairs
that embedding with the literal carrier equality.

It is the native source-charts side of Section 3 Claim 2's
contextual-profile transfer. It uses the verified root factorization,
literal source free amalgam and carrier equality theorems. It does
NOT assert a corresponding new geometric separator or the missing
opposite generated boundary after the inner replacement.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An actual old geometric outer piece can be recovered from its
nested source context WITH the entire original full functional
root and exact ordered source coordinates. This result concerns
the original source: the newly flipped source may not yet have
a geometric minimal separator on that same root. -/
theorem geometricOldOuterContext_exactRootedChart
    {V : Type}
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hInnerRoot : ∀ i : Fin m,
      d.roots i ∈ geometricPieceVertices Old P)
    (hInnerComponent :
      functionalComponentFrom Old (Set.range d.roots) d.left ⊆
        geometricPieceVertices Old P)
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Old
        (Set.range d.roots) d.left) :
    let Inner := (geometricGlobalFunctionalChart Old d).ext
    let E := geometricGlobalComplementChart Old d
    let S := oldOuterContextInInnerComplement Old P d
    let iInner : Structure.Embedding Inner.str Old :=
      functionalComponentEmbedding Old (Set.range d.roots)
        d.minimal.1 d.left
    let iE : Structure.Embedding E.str Old :=
      functionalComponentComplementEmbedding Old
        (Set.range d.roots) d.minimal.1 d.left
    let K : Set V :=
      iInner '' (Set.univ : Set Inner.Carrier) ∪ iE '' S
    ∃ (hK : Old.IsClosed K)
      (rK : Structure.Embedding
        (geometricGlobalFunctionalChart Old P).root
        (Old.induce K hK)),
      K = geometricPieceVertices Old P ∧
      ∀ i : Fin n, (rK i).1 = P.roots i := by
  classical
  let Inner := (geometricGlobalFunctionalChart Old d).ext
  let E := geometricGlobalComplementChart Old d
  let S := oldOuterContextInInnerComplement Old P d
  let iInner : Structure.Embedding Inner.str Old :=
    functionalComponentEmbedding Old (Set.range d.roots)
      d.minimal.1 d.left
  let iE : Structure.Embedding E.str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range d.roots) d.minimal.1 d.left
  have hOld : Structure.IsFreeAmalgam
      Inner.rootEmbedding E.rootEmbedding iInner iE :=
    geometricGlobalSource_freeDiagram Old d
  have hS : E.str.IsClosed S :=
    oldOuterContextInInnerComplement_isClosed Old P d
  have hRootS : ∀ r : Fin m, E.rootEmbedding r ∈ S :=
    oldOuterContext_contains_innerRoot Old P d hInnerRoot
  obtain ⟨hK, _rS, _jInner, jE, _hFreeK,
      _hInnerVal, hEval, _hRootVal⟩ :=
    fullFreeAmalgam_nestedContext_namedFullDiagram
      hOld S hS hRootS
  obtain ⟨rT, hRTval⟩ :=
    geometricOuterRoot_embedsFully_in_retainedComplement
      Old P d hOuterRootOutside
  have hCarrier :
      iInner '' (Set.univ : Set Inner.Carrier) ∪ iE '' S =
        geometricPieceVertices Old P :=
    geometricOldOuterContext_eq_outerPieceVertices
      Old P d hInnerRoot hInnerComponent
  let rK : Structure.Embedding
      (geometricGlobalFunctionalChart Old P).root
      (Old.induce
        (iInner '' (Set.univ : Set Inner.Carrier) ∪ iE '' S) hK) :=
    jE.comp rT
  refine ⟨hK, rK, hCarrier, ?_⟩
  intro i
  calc
    (rK i).1 = iE ((rT i).1) := hEval (rT i)
    _ = P.roots i := hRTval i

end AllThoseRamseyClasses.Lifts
