import AllThoseRamseyClasses.Lifts.GeometricFunctionalPieces
import AllThoseRamseyClasses.Lifts.FunctionalLiftLanguage
import PartiteConstruction.Structure.FreeAmalgamationClass

/-!
# Closed ordered roots in the 2019 functional piece language

An arbitrary rooted pattern is NOT automatically a full substructure
on its roots. The manuscript, however, roots each genuine piece in
a closed separating cut. Such a pattern induces an EXACT native
functional root structure on the standard carrier Fin n.

The new `rootStructure` pulls back old relation tuples and function
output memberships along the ordered root map. `rootInclusion`
is a FULL functional embedding precisely because its root set is
function-closed. Consequently no old function value or definedness
information is silently lost when replacing a concrete root set
by the canonical ordered coordinates Fin n.

Every geometrically selected forbidden piece supplies this
closedness via the full induced-piece embedding and the verified
closed-separator condition. This is the reusable root-chart
normalization required before the global equivalence-class lift
can be indexed solely by its arity.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {n : ℕ}

/-- A rooted pattern has a closed induced functional structure
on the exact range of its ordered tuple. -/
def FunctionalRootedPattern.IsRootClosed
    (P : FunctionalRootedPattern.{u,v} L n) : Prop :=
  P.str.IsClosed (Set.range P.root)

/-- The entire induced functional root structure, with the standard
ordered vertex carrier Fin n. The output set at a root input tuple
records EXACTLY the root coordinates of values in the source. -/
def FunctionalRootedPattern.rootStructure
    (P : FunctionalRootedPattern.{u,v} L n)
    (_hclosed : P.IsRootClosed) : Structure L (Fin n) where
  rel R xs := P.str.rel R (P.root ∘ xs)
  func F xs := {j | P.root j ∈ P.str.func F (P.root ∘ xs)}

/-- The ordered root map itself is a FULL native functional embedding
of its induced root structure. In particular old function fibres
are preserved and reflected, not just positive incidences. -/
def FunctionalRootedPattern.rootInclusion
    (P : FunctionalRootedPattern.{u,v} L n)
    (hclosed : P.IsRootClosed) :
    Structure.Embedding (P.rootStructure hclosed) P.str where
  toFun := P.root
  injective := P.root_injective
  map_rel_iff := fun _ _ => Iff.rfl
  map_func := by
    intro F xs
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      have hRange : y ∈ Set.range P.root :=
        hclosed F (P.root ∘ xs)
          (fun i => ⟨xs i, rfl⟩) hy
      rcases hRange with ⟨j, rfl⟩
      exact ⟨j, hy, rfl⟩

/-- Each ordered coordinate is preserved literally by the full
functional root embedding. -/
@[simp] theorem FunctionalRootedPattern.rootInclusion_apply
    (P : FunctionalRootedPattern.{u,v} L n)
    (hclosed : P.IsRootClosed) (i : Fin n) :
    P.rootInclusion hclosed i = P.root i := rfl

/-- In particular, the whole root set is the exact range of a
full embedding of a standard Fin n-carrier functional structure. -/
theorem FunctionalRootedPattern.rootEmbedding_range
    (P : FunctionalRootedPattern.{u,v} L n)
    (hclosed : P.IsRootClosed) :
    Set.range (P.rootInclusion hclosed) = Set.range P.root := rfl

/-- The actual source piece cut out by a minimal CLOSED separator
has a closed root, inherited by its full induced-piece embedding.
No unary-closure assumption is used. -/
theorem geometricFunctionalRootedPattern_rootClosed
    {V : Type v} (A : Structure L V) (n : ℕ)
    (d : GeometricFunctionalPieceData A n) :
    (geometricFunctionalRootedPattern A d).IsRootClosed := by
  let P := geometricFunctionalRootedPattern A d
  let E := geometricFunctionalPieceEmbedding A d
  have hCut : A.IsClosed (Set.range d.roots) := d.minimal.1
  have hPre : (geometricFunctionalPiece A d).IsClosed
      {x | E x ∈ Set.range d.roots} :=
    E.preimage_isClosed (Set.range d.roots) hCut
  have hRange :
      {x : P.Carrier | E x ∈ Set.range d.roots} =
        Set.range P.root := by
    ext x
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hi
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  change P.str.IsClosed {x | E x ∈ Set.range d.roots} at hPre
  rw [hRange] at hPre
  exact hPre

end AllThoseRamseyClasses.Lifts
