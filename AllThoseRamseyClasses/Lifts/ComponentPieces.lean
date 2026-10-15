import AllThoseRamseyClasses.Lifts.GaifmanCuts

/-!
# Extracting a rooted piece from a cut and a component

This is the concrete *relational carrier construction* in Definition
`defn:piece` of the 2019 paper. A tuple of pairwise distinct vertices
enumerates the deleted cut R, and a root of the complement selects an
actual connected component C of the Gaifman graph minus R.

The resulting structure is the exact structure induced on R ∪ C,
with its roots in their stipulated order. No vertices are silently
added by a closure hull. The construction is valid for any cut;
the paper only calls it a "piece" when R is a minimal separating
closed cut in a connected forbidden pattern. This additional
geometric condition is intentionally left to the next layer.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- The vertex set of the rooted structure cut out by a deleted
root tuple and a connected component of its complement. -/
def componentPieceVertices (A : RelStructure L V)
    {n : ℕ} (roots : Fin n → V)
    (baseRoot : {x : V // x ∉ Set.range roots}) : Set V :=
  Set.range roots ∪ componentFrom A (Set.range roots) baseRoot

/-- The exact induced rooted piece on R ∪ C, with the root tuple
enumerating R and no duplicate root vertices. -/
def componentPiece (A : RelStructure L V)
    {n : ℕ} (roots : Fin n → V)
    (hroots : Function.Injective roots)
    (baseRoot : {x : V // x ∉ Set.range roots}) :
    RootedPattern.{u,v} L n where
  Carrier := componentPieceVertices A roots baseRoot
  str := A.induce (componentPieceVertices A roots baseRoot)
  root := fun i => ⟨roots i, by
    change roots i ∈ Set.range roots ∪
      componentFrom A (Set.range roots) baseRoot
    exact Or.inl ⟨i, rfl⟩⟩
  root_injective := by
    intro i j h
    exact hroots (congrArg Subtype.val h)

/-- The piece really is an induced substructure of its source, so
the inclusion is a FULL relational embedding. -/
def componentPiece_inclusion (A : RelStructure L V)
    {n : ℕ} (roots : Fin n → V)
    (hroots : Function.Injective roots)
    (baseRoot : {x : V // x ∉ Set.range roots}) :
    Embedding (componentPiece A roots hroots baseRoot).str A :=
  A.inclusion (componentPieceVertices A roots baseRoot)

@[simp] theorem componentPiece_root_val (A : RelStructure L V)
    {n : ℕ} (roots : Fin n → V)
    (hroots : Function.Injective roots)
    (baseRoot : {x : V // x ∉ Set.range roots})
    (i : Fin n) :
    ((componentPiece A roots hroots baseRoot).root i).1 = roots i := rfl

/-- The image of the ordered root tuple is exactly the deleted cut,
not a proper subset or its generated closure. -/
theorem componentPiece_root_range (A : RelStructure L V)
    {n : ℕ} (roots : Fin n → V)
    (hroots : Function.Injective roots)
    (baseRoot : {x : V // x ∉ Set.range roots}) :
    Set.range (fun i => ((componentPiece A roots hroots baseRoot).root i).1)
      = Set.range roots := by
  rfl

/-- The component selected to form the piece is wholly inside its
induced vertex set. -/
theorem component_subset_pieceVertices (A : RelStructure L V)
    {n : ℕ} (roots : Fin n → V)
    (baseRoot : {x : V // x ∉ Set.range roots}) :
    componentFrom A (Set.range roots) baseRoot ⊆
      componentPieceVertices A roots baseRoot := by
  intro x hx
  exact Or.inr hx

/-- All neighbors of the selected component outside the component
are roots of the piece. This packages Observation `cuty` for the
actual rooted-piece vertex presentation. -/
theorem componentPiece_boundary_in_roots (A : RelStructure L V)
    {n : ℕ} (roots : Fin n → V)
    (baseRoot : {x : V // x ∉ Set.range roots}) :
    gaifmanNeighborhood A (componentFrom A (Set.range roots) baseRoot) ⊆
      Set.range roots :=
  gaifmanNeighborhood_component_subset_cut A (Set.range roots) baseRoot

end AllThoseRamseyClasses.Lifts
