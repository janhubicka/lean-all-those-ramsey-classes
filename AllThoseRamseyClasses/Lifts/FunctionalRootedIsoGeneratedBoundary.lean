import AllThoseRamseyClasses.Lifts.FunctionalRootedIsoGaifmanPaths
import AllThoseRamseyClasses.Lifts.FullEmbeddingGeneratedClosure

/-!
# Entire generated native component boundaries respect FULL rooted isomorphisms

The selected replacement Q used in a literal canonical 2019 flip
comes from a genuine geometric forbidden-source piece only up
to root-preserving FULL isomorphism of the entire native
function-graph language. We must transport not merely a graph
component, but its complete external Gaifman neighbourhood
and full generated function closure.

This module proves exact neighbourhood image under such an
isomorphism (both inclusions, using the inverse for reflection).
The verified FULL functional-embedding closure theorem then
gives exact equality of the entire generated boundaries.
No assumption that an arbitrary non-onto induced embedding
reflects ambient Gaifman edges is made.

The next theorem will apply these formulas to the one actual
selected component in the genuine source witness from #766.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {n : ℕ}
variable {P Q : FunctionalRootedPattern.{u,v} L n}

/-- The ENTIRE Gaifman external neighbourhood of any set of
native source vertices is mapped exactly by an onto FULL
rooted functional isomorphism; arbitrary positive function
incidence tuples are reflected as well as preserved. -/
theorem functionalRootedIso_gaifmanNeighborhood_image
    (e : FunctionalRootedPatternIso P Q)
    (C : Set P.Carrier) :
    gaifmanNeighborhood Q.str.graph (e.equiv '' C) =
      e.equiv '' gaifmanNeighborhood P.str.graph C := by
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨hyNotC, z, ⟨c, hc, hz⟩, hzy⟩ := hy
    obtain ⟨x, rfl⟩ := e.equiv.surjective y
    have hcNotY : x ∉ C := by
      intro hxC
      exact hyNotC ⟨x, hxC, rfl⟩
    have hEdgeP : GaifmanAdjacent P.str.graph c x := by
      have hEdgeQ : GaifmanAdjacent Q.str.graph
          (e.equiv c) (e.equiv x) := by
        rw [hz]
        exact hzy
      have hBack := functionalRootedIso_gaifmanAdjacent_map
        e.symm hEdgeQ
      change GaifmanAdjacent P.str.graph
        (e.equiv.symm (e.equiv c)) (e.equiv.symm (e.equiv x)) at hBack
      simpa only [e.equiv.symm_apply_apply] using hBack
    exact ⟨x, ⟨hcNotY, c, hc, hEdgeP⟩, rfl⟩
  · rintro y ⟨x, ⟨hxNotC, c, hc, hcx⟩, rfl⟩
    have hxNotImage : e.equiv x ∉ e.equiv '' C := by
      rintro ⟨d, hd, hdx⟩
      have hdEq : d = x := e.equiv.injective hdx
      exact hxNotC (hdEq ▸ hd)
    have hEdgeQ : GaifmanAdjacent Q.str.graph
        (e.equiv c) (e.equiv x) :=
      functionalRootedIso_gaifmanAdjacent_map e hcx
    exact ⟨hxNotImage, e.equiv c, ⟨c, hc, rfl⟩, hEdgeQ⟩

/-- Equality of the COMPLETE function-generated external boundary
for any source subset under a full rooted functional isomorphism.
This retains all native partial-function value fibres, including
nullary symbols. -/
theorem functionalRootedIso_generatedBoundary_image
    (e : FunctionalRootedPatternIso P Q)
    (C : Set P.Carrier) :
    Q.str.functionClosure
      (gaifmanNeighborhood Q.str.graph (e.equiv '' C)) =
      e.equiv ''
        (P.str.functionClosure
          (gaifmanNeighborhood P.str.graph C)) := by
  apply functionalEmbedding_generatedBoundary_image
    P.str Q.str e.toFullEmbedding C
  exact functionalRootedIso_gaifmanNeighborhood_image e C

/-- The source and target components are IDENTICAL through a genuine
onto full rooted functional isomorphism, not just contained one
in another. The inverse map transports every root-avoiding path
back, so no extra target component vertices are introduced. -/
theorem functionalRootedIso_component_image_eq
    (e : FunctionalRootedPatternIso P Q)
    (x : {a : P.Carrier // a ∉ Set.range P.root}) :
    e.equiv ''
      componentFrom P.str.graph (Set.range P.root) x =
    componentFrom Q.str.graph (Set.range Q.root)
      (functionalRootedIso_outsideRoot e x) := by
  apply Set.Subset.antisymm
  · exact functionalRootedIso_component_image_subset e x
  · intro z hz
    let xQ := functionalRootedIso_outsideRoot e x
    have hBack :
        e.equiv.symm z ∈
          componentFrom P.str.graph (Set.range P.root)
            (functionalRootedIso_outsideRoot e.symm xQ) := by
      have hin :
          e.equiv.symm z ∈
            e.equiv.symm ''
              componentFrom Q.str.graph (Set.range Q.root) xQ :=
        ⟨z, hz, rfl⟩
      exact functionalRootedIso_component_image_subset e.symm xQ hin
    have hRootBack :
        functionalRootedIso_outsideRoot e.symm xQ = x := by
      apply Subtype.ext
      exact e.equiv.symm_apply_apply x.1
    rw [hRootBack] at hBack
    exact ⟨e.equiv.symm z, hBack,
      e.equiv.apply_symm_apply z⟩

/-- Exact equality of COMPLETE generated component boundaries under
a genuine full rooted functional isomorphism. Both the component
and every generated function-value vertex are transported, with no
substructure reflection shortcut. -/
theorem functionalRootedIso_componentGeneratedBoundary_image
    (e : FunctionalRootedPatternIso P Q)
    (x : {a : P.Carrier // a ∉ Set.range P.root}) :
    Q.str.functionClosure
      (gaifmanNeighborhood Q.str.graph
        (componentFrom Q.str.graph (Set.range Q.root)
          (functionalRootedIso_outsideRoot e x))) =
      e.equiv ''
        (P.str.functionClosure
          (gaifmanNeighborhood P.str.graph
            (componentFrom P.str.graph (Set.range P.root) x))) := by
  rw [← functionalRootedIso_component_image_eq e x]
  exact functionalRootedIso_generatedBoundary_image e
    (componentFrom P.str.graph (Set.range P.root) x)


end AllThoseRamseyClasses.Lifts
