import AllThoseRamseyClasses.Lifts.FunctionalRootedIsoEmbedding
import AllThoseRamseyClasses.Lifts.SeparatorPaths

/-!
# Root-preserving functional isomorphisms transport exact Gaifman paths

A selected replacement piece in the original 2019 global canonical
lift is represented by a genuine finite forbidden geometric piece
only UP TO A FULL ROOTED ISOMORPHISM of the complete original
function-graph language. Track A must transport the genuine selected
component, not assume that a generic equivalent root extension has
a connected complement of its roots.

The present module provides the independent source-functional
geometry API for such transport: exact Gaifman edges, root
complements, and paths avoiding the FULL ordered root. This uses
the relationalized graph isomorphism, whose relation symbols include
the complete input/output incidences of every native function.
Thus the proof admits arbitrary function arities and repeated
coordinates, and does not identify different source vertices
through a weak forbidden target map.

Preservation of the entire generated neighbourhood boundary and
the NEW full-amalgam geometric chart are separate obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {n : ℕ}
variable {P Q : FunctionalRootedPattern.{u,v} L n}

/-- A true FULL rooted functional isomorphism maps every complete
source Gaifman edge to an actual target Gaifman edge, including
edges witnessed by function graph tuples. -/
theorem functionalRootedIso_gaifmanAdjacent_map
    (e : FunctionalRootedPatternIso P Q)
    {x y : P.Carrier}
    (hxy : GaifmanAdjacent P.str.graph x y) :
    GaifmanAdjacent Q.str.graph (e.equiv x) (e.equiv y) := by
  rcases hxy with ⟨hne, s, t, i, j, ht, hti, htj⟩
  refine ⟨fun heq => hne (e.equiv.injective heq),
    s, e.equiv ∘ t, i, j, ?_, ?_, ?_⟩
  · exact (e.rel_iff s t).mpr ht
  · exact congrArg e.equiv hti
  · exact congrArg e.equiv htj

/-- A vertex outside the entire ordered root remains outside the
entire ordered target root under a root-preserving isomorphism.
No extra generated-closure root vertices are silently inserted. -/
def functionalRootedIso_outsideRoot
    (e : FunctionalRootedPatternIso P Q)
    (x : {a : P.Carrier // a ∉ Set.range P.root}) :
    {b : Q.Carrier // b ∉ Set.range Q.root} :=
  ⟨e.equiv x.1, by
    rintro ⟨i, hi⟩
    apply x.2
    refine ⟨i, ?_⟩
    apply e.equiv.injective
    calc
      e.equiv (P.root i) = Q.root i := e.roots i
      _ = e.equiv x.1 := hi⟩

/-- All actual source paths avoiding the root transport through
the full rooted graph/function isomorphism, including zero-length
paths. The image path avoids the COMPLETE new ordered root. -/
theorem functionalRootedIso_reachOutside_map
    (e : FunctionalRootedPatternIso P Q)
    {x y : {a : P.Carrier // a ∉ Set.range P.root}}
    (h : ReachOutside P.str.graph (Set.range P.root) x y) :
    ReachOutside Q.str.graph (Set.range Q.root)
      (functionalRootedIso_outsideRoot e x)
      (functionalRootedIso_outsideRoot e y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b hpath hedge ih =>
      have hstep :
          outsideAdjacency Q.str.graph (Set.range Q.root)
            (functionalRootedIso_outsideRoot e a)
            (functionalRootedIso_outsideRoot e b) :=
        functionalRootedIso_gaifmanAdjacent_map e hedge
      exact ih.tail hstep

/-- The full image of one source component after deleting its
complete root lies in the corresponding component after deleting
the target root. The reverse inclusion follows by applying this
statement to e.symm; no non-full induced-graph embedding is used. -/
theorem functionalRootedIso_component_image_subset
    (e : FunctionalRootedPatternIso P Q)
    (x : {a : P.Carrier // a ∉ Set.range P.root}) :
    e.equiv ''
      componentFrom P.str.graph (Set.range P.root) x ⊆
    componentFrom Q.str.graph (Set.range Q.root)
      (functionalRootedIso_outsideRoot e x) := by
  rintro y ⟨a, ⟨haRoot, haReach⟩, rfl⟩
  let aOut : {a : P.Carrier // a ∉ Set.range P.root} :=
    ⟨a, haRoot⟩
  exact ⟨(functionalRootedIso_outsideRoot e aOut).2,
    functionalRootedIso_reachOutside_map e haReach⟩

end AllThoseRamseyClasses.Lifts
