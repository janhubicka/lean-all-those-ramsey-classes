import AllThoseRamseyClasses.Lifts.MinimalSeparatorReverse
import AllThoseRamseyClasses.Lifts.ComponentPieces

/-!
# Actual rooted pieces selected by minimal functional separators

The geometric construction of Definition `defn:piece` in Section 3
of Hubička--Nešetřil, *All those Ramsey classes* (2019).

A cut is an exact set of vertices enumerated by distinct roots.
We require it to be a minimal *closed* separator of two surviving
components, using the now verified Proposition `prop:sep` interface.
One of these components supplies the vertices of the piece.
The resulting induced structure really is closed for the full
function signature, and its relationalized graph agrees with the
existing `RootedPattern` library.

This is a source-attached geometric piece. The extra step of taking
all such pieces of members of the forbidden family, modulo rooted
isomorphism, is separate; no assertion of maximality or a flip lemma
is hidden in the definitions below.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v

variable {L : Language.{u}} {V : Type v}

/-- Concrete data witnessing a piece of A, with its root tuple
enumerating a minimal closed separator. Choosing two components
makes the manuscript's `minimal separating cut` requirement
explicit rather than treating an arbitrary cut as a piece. -/
structure GeometricFunctionalPieceData
    (A : Structure L V) (n : ℕ) where
  roots : Fin n → V
  roots_injective : Function.Injective roots
  left : {x : V // x ∉ Set.range roots}
  right : {x : V // x ∉ Set.range roots}
  minimal : IsMinimalClosedSeparator A (Set.range roots) left right

/-- The exact closed root set, without replacing it by its
generated hull or forgetting the prescribed order. -/
abbrev geometricPieceCut (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n) : Set V :=
  Set.range d.roots

/-- The selected component together with the original cut. -/
abbrev geometricPieceVertices (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n) : Set V :=
  functionalComponentUnion A (geometricPieceCut A d) d.left

/-- The actual induced functional structure on the piece, which
exists because the root set is closed and the component-union
closure lemma is proved. -/
def geometricFunctionalPiece (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n) :
    Structure L (geometricPieceVertices A d) :=
  functionalComponentInduce A (geometricPieceCut A d) d.minimal.1 d.left

/-- The inclusion of the concrete piece into its forbidden witness
is a FULL functional embedding, not a weak map. -/
def geometricFunctionalPieceEmbedding (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n) :
    Structure.Embedding (geometricFunctionalPiece A d) A :=
  functionalComponentEmbedding A (geometricPieceCut A d) d.minimal.1 d.left

/-- The identical piece, now in the graph-encoded relation language,
with ordered roots. Existing piece-lift constructions can take
this as their rooted pattern. -/
def geometricRootedGraphPiece (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n) :
    RootedPattern.{u,v} L.graph n where
  Carrier := geometricPieceVertices A d
  str := (geometricFunctionalPiece A d).graph
  root := fun i => ⟨d.roots i, by
    change d.roots i ∈
      (Set.range d.roots ∪
        componentFrom A.graph (Set.range d.roots) d.left)
    exact Or.inl ⟨i, rfl⟩⟩
  root_injective := by
    intro i j h
    exact d.roots_injective (congrArg Subtype.val h)

/-- The graph of the genuinely induced functional piece is literally
the relationally induced rooted pattern's underlying structure.
The equality includes nullary relations and function graph tuples. -/
theorem geometricFunctionalPiece_graph
    (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n) :
    (geometricFunctionalPiece A d).graph =
      (geometricRootedGraphPiece A d).str := by
  rfl

/-- The two selected components of the original closed cut are
disjoint; they cannot accidentally describe the same piece side. -/
theorem geometricPiece_components_disjoint
    (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n) :
    Disjoint
      (componentFrom A.graph (geometricPieceCut A d) d.left)
      (componentFrom A.graph (geometricPieceCut A d) d.right) :=
  componentFrom_disjoint_of_not_reach A.graph
    (geometricPieceCut A d) d.left d.right d.minimal.2.1

/-- The first component's entire boundary generates exactly the
original closed root set: the first equation in `prop:sep`. -/
theorem geometricPiece_left_boundary_closure
    (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n) :
    A.functionClosure
      (gaifmanNeighborhood A.graph
        (componentFrom A.graph (geometricPieceCut A d) d.left)) =
      geometricPieceCut A d :=
  (minimalClosedSeparator_bothBoundaries_eq A
    (geometricPieceCut A d) d.left d.right d.minimal).1

/-- The second complementary component has the same generated
boundary, as required by minimal separating cut geometry. -/
theorem geometricPiece_right_boundary_closure
    (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n) :
    A.functionClosure
      (gaifmanNeighborhood A.graph
        (componentFrom A.graph (geometricPieceCut A d) d.right)) =
      geometricPieceCut A d :=
  (minimalClosedSeparator_bothBoundaries_eq A
    (geometricPieceCut A d) d.left d.right d.minimal).2

end AllThoseRamseyClasses.Lifts
