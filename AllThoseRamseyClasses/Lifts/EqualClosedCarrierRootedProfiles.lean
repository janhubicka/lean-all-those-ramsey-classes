import AllThoseRamseyClasses.Lifts.FunctionalRootedIsoProfileTransport
import PartiteConstruction.Functional.WeakOperations

/-!
# Exact rooted isomorphism between induced full native functional sources

Given two equal closed vertex subsets of the SAME full native
functional source, their induced structures are fully isomorphic,
regardless of the actual proof terms establishing closedness.

If two full rooted charts over the same root have identical original
vertex coordinates, the isomorphism respects the entire root.
Consequently ALL existential forbidden-rooted diagram tests agree,
without any isomorphism closure of the forbidden family.

This is the source-carrier bridge from an old geometric piece to
its old transported closed context once exact vertex-set equality
has been proved. Nothing is assumed about graph-only substructures,
weak target images, or geometric minimal separators.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Equal function-closed subsets of one full functional source
give an onto full native embedding of their induced structures.
It preserves every vertex of the common source literally. -/
theorem equalClosedCarrier_hasFullInducedIso
    {V R : Type v}
    (A : Structure L V)
    (S T : Set V)
    (hS : A.IsClosed S) (hT : A.IsClosed T)
    (hST : S = T)
    (Root : Structure L R)
    (rS : Structure.Embedding Root (A.induce S hS))
    (rT : Structure.Embedding Root (A.induce T hT))
    (hRoot : ∀ r : R, (rS r).1 = (rT r).1) :
    ∃ e : Structure.Embedding (A.induce S hS) (A.induce T hT),
      Function.Surjective e ∧
      (∀ s : S, (e s).1 = s.1) ∧
      (∀ r : R, e (rS r) = rT r) := by
  classical
  let incS : Structure.Embedding (A.induce S hS) A :=
    Structure.inclusion A S hS
  let incT : Structure.Embedding (A.induce T hT) A :=
    Structure.inclusion A T hT
  let f : S → T := fun s =>
    ⟨s.1, by simpa only [← hST] using s.2⟩
  have hf : ∀ s : S, incS s = incT (f s) := by
    intro s
    rfl
  let e : Structure.Embedding (A.induce S hS) (A.induce T hT) :=
    incS.factorWithMap incT f hf
  have hValue : ∀ s : S, (e s).1 = s.1 := by
    intro s
    rfl
  have hSurj : Function.Surjective e := by
    intro t
    let s : S :=
      ⟨t.1, by simpa only [hST] using t.2⟩
    refine ⟨s, ?_⟩
    apply Subtype.ext
    exact hValue s
  have hRespect : ∀ r : R, e (rS r) = rT r := by
    intro r
    apply Subtype.ext
    exact (hValue (rS r)).trans (hRoot r)
  exact ⟨e, hSurj, hValue, hRespect⟩

/-- Identical full-rooted vertex coordinates on equal closed
subsets imply equality of their COMPLETE forbidden diagram
profiles. Even if the induced closedness proofs differ, all old
relations and whole function fibres agree by full isomorphism. -/
theorem equalClosedCarrier_rootedProfiles_equiv
    {V R : Type}
    (A : Structure L V)
    (S T : Set V)
    (hS : A.IsClosed S) (hT : A.IsClosed T)
    (hST : S = T)
    (Root : Structure L R)
    (rS : Structure.Embedding Root (A.induce S hS))
    (rT : Structure.Embedding Root (A.induce T hT))
    (hRoot : ∀ r : R, (rS r).1 = (rT r).1)
    (F : ∀ {W : Type}, Structure L W → Prop) :
    (functionalDiagramPieceSetoid Root F).r
      ({ Carrier := S, str := A.induce S hS,
         rootEmbedding := rS } : FunctionalRootExtension Root)
      ({ Carrier := T, str := A.induce T hT,
         rootEmbedding := rT } : FunctionalRootExtension Root) := by
  obtain ⟨e, heSurj, _heValues, heRoot⟩ :=
    equalClosedCarrier_hasFullInducedIso A S T hS hT
      hST Root rS rT hRoot
  exact functionalDiagramPiece_equiv_of_ontoRootIso
    Root F
    ({ Carrier := S, str := A.induce S hS,
       rootEmbedding := rS } : FunctionalRootExtension Root)
    ({ Carrier := T, str := A.induce T hT,
       rootEmbedding := rT } : FunctionalRootExtension Root)
    e heSurj heRoot

end AllThoseRamseyClasses.Lifts
