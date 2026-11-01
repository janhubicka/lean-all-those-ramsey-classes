import AllThoseRamseyClasses.Lifts.GeometricFlipGlobalSymbolCongruence
import AllThoseRamseyClasses.Lifts.PrescribedGeometricOuterRoot

/-!
# Full geometric-boundary premises imply preservation of the global symbol

This is the assembled source-level endgame of Track B's portion
of Section 3 Claim 2.  The old outer-root tuple survives in the
complete retained complement of an actual functional inner flip.

A *genuine new geometric piece* is no longer an extra argument:
from the exact separated outside-root components, both complete
function-generated boundary equalities, and equality of the
transported context with the whole new selected component plus
the old root, we CONSTRUCT the geometric piece using the unchanged
original ordered Fin n root. The verified Track B symbol theorem
then gives literal equality in the 2019 GLOBAL canonical lift
piece-symbol quotient.

The preserved root is automatically injective and function-closed
from the full native retained-complement embedding; no extra
root-structure assumption is added.

Important: the path/component/boundary premises are NOT proved
for arbitrary nested flips here. The missing opposite-boundary
and exact whole-component geometry remains Track A's obligation.
This is not an unrestricted Claim 2 or strong-amalgamation theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The old ordered outer root's image in the NEW source is injective
and FULLY function-closed, as it factors through a genuine full
functional embedding of the unchanged complement.

No assumption on how the two old root sets are nested and no
relation-only approximation. -/
theorem geometricTransportedOuterRoot_closed_and_injective
    {V W : Type}
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Old
        (Set.range d.roots) d.left)
    (New : Structure L W)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old d).str New) :
    let roots : Fin n → W :=
      fun i => iE
        (⟨P.roots i, hOuterRootOutside i⟩ :
          (geometricGlobalComplementChart Old d).Carrier)
    New.IsClosed (Set.range roots) ∧ Function.Injective roots := by
  classical
  let E := geometricGlobalComplementChart Old d
  let S := oldOuterContextInInnerComplement Old P d
  have hS : E.str.IsClosed S :=
    oldOuterContextInInnerComplement_isClosed Old P d
  let Root := (geometricGlobalFunctionalChart Old P).root
  let roots : Fin n → W :=
    fun i => iE (⟨P.roots i, hOuterRootOutside i⟩ : E.Carrier)
  obtain ⟨rT, hrT⟩ :=
    geometricOuterRoot_embedsFully_in_retainedComplement
      Old P d hOuterRootOutside
  let incS : Structure.Embedding (E.str.induce S hS) E.str :=
    Structure.inclusion E.str S hS
  let e : Structure.Embedding Root New :=
    iE.comp (incS.comp rT)
  have he (i : Fin n) : e i = roots i := by
    change iE ((rT i).1) =
      iE (⟨P.roots i, hOuterRootOutside i⟩ : E.Carrier)
    apply congrArg iE
    apply Subtype.ext
    exact hrT i
  have hUniv : Root.IsClosed (Set.univ : Set (Fin n)) := by
    intro Fn args hargs y hy
    exact Set.mem_univ _
  have hClosedE : New.IsClosed (Set.range e) := by
    simpa only [Set.image_univ] using
      (functionalEmbedding_image_closed Root New e
        (Set.univ : Set (Fin n)) hUniv)
  have hRange : Set.range e = Set.range roots := by
    exact congrArg Set.range (funext he)
  have hClosedRoots : New.IsClosed (Set.range roots) := by
    rw [← hRange]
    exact hClosedE
  have hInj : Function.Injective roots := by
    intro i j hij
    apply P.roots_injective
    have heij :
        (⟨P.roots i, hOuterRootOutside i⟩ : E.Carrier) =
        (⟨P.roots j, hOuterRootOutside j⟩ : E.Carrier) :=
      iE.injective hij
    exact congrArg Subtype.val heij
  exact ⟨hClosedRoots, hInj⟩

/-- Entire ordered source-level Claim 2 symbol preservation,
CONDITIONAL ONLY ON the genuine new outer-component geometry
and inner all-test-equivalence premises.

The resulting Pnew is really a minimal-closed-separator piece
in the NEW forbidden source, on the original Fin n root.
Consequently its published global quotient index agrees with
the original outer geometric piece. -/
theorem geometricFlip_globalPieceSymbol_of_exactOppositeBoundaries
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {V W : Type} [Finite V] [Finite W]
    (Old : Structure L V) (hFOld : F Old)
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
        (Set.range d.roots) d.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old d).root)
    (hEq : (functionalDiagramPieceSetoid
      (geometricGlobalFunctionalChart Old d).root F).r
        (geometricGlobalFunctionalChart Old d).ext Q)
    (New : Structure L W) (hFNew : F New)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old d).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old d).rootEmbedding iQ iE)
    (roots : Fin n → W)
    (hRootCoordinates : ∀ i : Fin n,
      roots i =
        iE (⟨P.roots i, hOuterRootOutside i⟩ :
          (geometricGlobalComplementChart Old d).Carrier))
    (x y : {w : W // w ∉ Set.range roots})
    (hSeparated : ¬ ReachOutside New.graph (Set.range roots) x y)
    (hLeftBoundary :
      New.functionClosure
        (gaifmanNeighborhood New.graph
          (componentFrom New.graph (Set.range roots) x)) =
          Set.range roots)
    (hRightBoundary :
      New.functionClosure
        (gaifmanNeighborhood New.graph
          (componentFrom New.graph (Set.range roots) y)) =
          Set.range roots)
    (hExactContext :
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old P d)) =
        Set.range roots ∪
          componentFrom New.graph (Set.range roots) x)
    (hn : 0 < n) :
    ∃ Pnew : GeometricFunctionalPieceData New n,
      (∀ i : Fin n,
        Pnew.roots i =
          iE (⟨P.roots i, hOuterRootOutside i⟩ :
            (geometricGlobalComplementChart Old d).Carrier)) ∧
      geometricGlobalPieceSymbol F Old
          (inferInstance : Finite V) hFOld P hn =
        geometricGlobalPieceSymbol F New
          (inferInstance : Finite W) hFNew Pnew hn := by
  classical
  let root0 : Fin n → W :=
    fun i => iE
      (⟨P.roots i, hOuterRootOutside i⟩ :
        (geometricGlobalComplementChart Old d).Carrier)
  obtain ⟨hClosed0, hInj0⟩ :=
    geometricTransportedOuterRoot_closed_and_injective
      Old P d hOuterRootOutside New iE
  have hRootEq : roots = root0 := funext hRootCoordinates
  have hClosed : New.IsClosed (Set.range roots) := by
    rw [hRootEq]
    exact hClosed0
  have hInj : Function.Injective roots := by
    rw [hRootEq]
    exact hInj0
  let K : Set W :=
    iQ '' (Set.univ : Set Q.Carrier) ∪
      iE '' (oldOuterContextInInnerComplement Old P d)
  obtain ⟨Pnew, hPnewRoot, _hX, _hY, hPnewCarrier⟩ :=
    geometricPiece_of_prescribedRoot_and_exactBoundaries
      New roots hInj hClosed x y hSeparated
      hLeftBoundary hRightBoundary K hExactContext
  refine ⟨Pnew, ?_, ?_⟩
  · intro i
    exact (congrFun hPnewRoot i).trans (hRootCoordinates i)
  · apply geometricFlip_preserves_globalPieceSymbol_of_newGeometricContext
      F Old hFOld P d hInnerRoot hInnerComponent
      hOuterRootOutside Q hEq New hFNew iQ iE hFree
      Pnew
    · intro i
      exact (congrFun hPnewRoot i).trans (hRootCoordinates i)
    · exact hPnewCarrier.symm

end AllThoseRamseyClasses.Lifts
