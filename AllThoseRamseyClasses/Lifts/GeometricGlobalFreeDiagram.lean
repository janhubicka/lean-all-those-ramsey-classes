import AllThoseRamseyClasses.Lifts.GeometricGlobalPieceSymbol
import AllThoseRamseyClasses.Lifts.FreeAmalgamRootReparam
import AllThoseRamseyClasses.Lifts.FreeAmalgamSideIso
import AllThoseRamseyClasses.Lifts.GeometricPieceRootChart

/-!
# Normalize an actual forbidden source to its GLOBAL Fin n root chart

The geometric minimal-separator piece of the 2019 lift already has a
complete functional structure on its ordered root tuple Fin n.
The original source free-amalgam diagram, however, is initially
over the literal closed separator subtype R.

Factor the geometric root tuple through the verified full root
inclusion into the source piece, obtaining a FULL ONTO functional
embedding of the standard Fin n root onto the original cut R.
Transport the exact free-amalgam diagram along this root isomorphism.

The resulting left extension is the actual globally selected
geometric piece; its right extension is the original closed
complement. The forbidden source is literally unchanged, not
reconstructed by a particular canonical pushout implementation.

This is the missing source geometry for applying a selected GLOBAL
canonical class witness directly to a forbidden-source flip.
No arbitrary weak map is promoted to a full embedding.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V : Type} {n : ℕ}

/-- Identify the complete functional root of a geometric piece
on ordered Fin n with the exact induced structure on its closed
separator in the original forbidden source. -/
def geometricGlobalRootEmbedding
    (A : Structure L V) (d : GeometricFunctionalPieceData A n) :
    Structure.Embedding
      (geometricGlobalFunctionalChart A d).root
      (closedCutRoot A (Set.range d.roots) d.minimal.1) := by
  let P := geometricGlobalFunctionalChart A d
  let r : Fin n → Set.range d.roots :=
    fun i => ⟨d.roots i, ⟨i, rfl⟩⟩
  let oldRoot := componentRootToPiece A (Set.range d.roots)
    d.minimal.1 d.left
  exact P.ext.rootEmbedding.factorWithMap oldRoot r (by
    intro i
    rfl)

/-- The ordered finite root covers the entire original separating
cut exactly. It does not add any generated-closure vertex. -/
theorem geometricGlobalRootEmbedding_surjective
    (A : Structure L V) (d : GeometricFunctionalPieceData A n) :
    Function.Surjective (geometricGlobalRootEmbedding A d) := by
  intro x
  rcases x.property with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  apply Subtype.ext
  change d.roots i = x.1
  exact hi

/-- The original complementary side as an extension of the selected
piece's standard ordered full functional root, not merely a root
tuple with equal cardinality. -/
def geometricGlobalComplementChart
    (A : Structure L V) (d : GeometricFunctionalPieceData A n) :
    FunctionalRootExtension (geometricGlobalFunctionalChart A d).root where
  Carrier := Set.compl (functionalComponentFrom A (Set.range d.roots) d.left)
  str := functionalComponentComplementInduce A (Set.range d.roots)
    d.minimal.1 d.left
  rootEmbedding :=
    (componentRootToComplement A (Set.range d.roots)
      d.minimal.1 d.left).comp
      (geometricGlobalRootEmbedding A d)

/-- The ORIGINAL forbidden source is a complete functional free
amalgam of its globally selected geometric piece and its closed
complement over their common standard Fin n root. -/
theorem geometricGlobalSource_freeDiagram
    (A : Structure L V) (d : GeometricFunctionalPieceData A n) :
    Structure.IsFreeAmalgam
      (geometricGlobalFunctionalChart A d).ext.rootEmbedding
      (geometricGlobalComplementChart A d).rootEmbedding
      (functionalComponentEmbedding A (Set.range d.roots)
        d.minimal.1 d.left)
      (functionalComponentComplementEmbedding A (Set.range d.roots)
        d.minimal.1 d.left) := by
  let oldLeft := componentRootToPiece A (Set.range d.roots)
    d.minimal.1 d.left
  let oldRight := componentRootToComplement A (Set.range d.roots)
    d.minimal.1 d.left
  let incLeft := functionalComponentEmbedding A (Set.range d.roots)
    d.minimal.1 d.left
  let incRight := functionalComponentComplementEmbedding A (Set.range d.roots)
    d.minimal.1 d.left
  let k := geometricGlobalRootEmbedding A d
  have hfree :
      Structure.IsFreeAmalgam
        (oldLeft.comp k) (oldRight.comp k) incLeft incRight :=
    freeAmalgam_precompose_root_onto
      (component_isFreeAmalgam A (Set.range d.roots)
        d.minimal.1 d.left)
      k (geometricGlobalRootEmbedding_surjective A d)
  have hroot : ∀ i : Fin n,
      (Structure.Embedding.id
        (geometricFunctionalPiece A d))
          ((geometricGlobalFunctionalChart A d).ext.rootEmbedding i) =
        (oldLeft.comp k) i := by
    intro i
    rfl
  have hId : Function.Surjective
      (Structure.Embedding.id (geometricFunctionalPiece A d)) := by
    intro x
    exact ⟨x, rfl⟩
  exact freeAmalgam_precompose_left_iso hfree
    (Structure.Embedding.id (geometricFunctionalPiece A d))
    hId
    (geometricGlobalFunctionalChart A d).ext.rootEmbedding
    hroot

/-- Every finite forbidden source with a geometric piece supplies
an actual forbidden full source diagram over its GLOBAL root chart.
The right-hand test need not itself be a forbidden piece. -/
theorem geometricGlobalSource_has_forbidden_diagram
    (F : ∀ {W : Type}, Structure L W → Prop)
    (A : Structure L V) (hFinite : Finite V) (hFA : F A)
    (d : GeometricFunctionalPieceData A n) :
    forbiddenFunctionalDiagram
      (geometricGlobalSelectedChart F A hFinite hFA d).1.root
      F
      (geometricGlobalSelectedChart F A hFinite hFA d).1.ext
      (geometricGlobalComplementChart A d) := by
  exact ⟨V, A, hFA,
    functionalComponentEmbedding A (Set.range d.roots)
      d.minimal.1 d.left,
    functionalComponentComplementEmbedding A (Set.range d.roots)
      d.minimal.1 d.left,
    geometricGlobalSource_freeDiagram A d⟩

end AllThoseRamseyClasses.Lifts
