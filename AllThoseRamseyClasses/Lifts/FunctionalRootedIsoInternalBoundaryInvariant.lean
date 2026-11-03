import AllThoseRamseyClasses.Lifts.FunctionalRootedIsoGeneratedBoundary

/-!
# Exact internal-root boundary is invariant under full rooted functional isomorphism

The canonical global 2019 lift selects a genuine forbidden
geometric piece only up to a FULL root-preserving isomorphism
of the entire native function-graph language. The original
selected piece will have its internal component-boundary
equation derived from the whole forbidden source (Track A
#797/#799). This module transports THAT equation to the
SAME replacement Q, without changing its root coordinates.

The proof uses equality of COMPLETE source component images
and COMPLETE function-generated external boundary images, not
an invalid reflection by arbitrary non-onto embeddings.
All arities and nullary function outputs are preserved.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {n : ℕ}
variable {P Q : FunctionalRootedPattern.{u,v} L n}

/-- A genuine root-preserving full functional isomorphism maps
the FULL ordered root range onto exactly the target root range. -/
theorem functionalRootedIso_rootRange_image
    (e : FunctionalRootedPatternIso P Q) :
    e.equiv '' Set.range P.root = Set.range Q.root := by
  ext z
  constructor
  · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (e.roots i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨P.root i, ⟨i, rfl⟩, e.roots i⟩

/-- Transport existence of ONE genuine selected component whose
entire generated external boundary is exactly the FULL ordered
root. This is the source-side component invariant required for
the 2019 forbidden replacement Q. -/
theorem functionalRootedIso_internalBoundary_forward
    (e : FunctionalRootedPatternIso P Q)
    (hP :
      ∃ x : {v : P.Carrier // v ∉ Set.range P.root},
        P.str.functionClosure
          (gaifmanNeighborhood P.str.graph
            (componentFrom P.str.graph (Set.range P.root) x)) =
          Set.range P.root) :
    ∃ y : {v : Q.Carrier // v ∉ Set.range Q.root},
      Q.str.functionClosure
        (gaifmanNeighborhood Q.str.graph
          (componentFrom Q.str.graph (Set.range Q.root) y)) =
        Set.range Q.root := by
  obtain ⟨x, hBound⟩ := hP
  refine ⟨functionalRootedIso_outsideRoot e x, ?_⟩
  rw [functionalRootedIso_componentGeneratedBoundary_image e x, hBound]
  exact functionalRootedIso_rootRange_image e

/-- Equality of a whole root with a generated external component
boundary is invariant in BOTH directions under a genuine full
root-preserving isomorphism. Neither direction invokes an arbitrary
forbidden-image or target-map quotient. -/
theorem functionalRootedIso_internalBoundary_iff
    (e : FunctionalRootedPatternIso P Q) :
    (∃ x : {v : P.Carrier // v ∉ Set.range P.root},
      P.str.functionClosure
        (gaifmanNeighborhood P.str.graph
          (componentFrom P.str.graph (Set.range P.root) x)) =
        Set.range P.root) ↔
    (∃ y : {v : Q.Carrier // v ∉ Set.range Q.root},
      Q.str.functionClosure
        (gaifmanNeighborhood Q.str.graph
          (componentFrom Q.str.graph (Set.range Q.root) y)) =
        Set.range Q.root) := by
  constructor
  · exact functionalRootedIso_internalBoundary_forward e
  · exact functionalRootedIso_internalBoundary_forward e.symm

end AllThoseRamseyClasses.Lifts
