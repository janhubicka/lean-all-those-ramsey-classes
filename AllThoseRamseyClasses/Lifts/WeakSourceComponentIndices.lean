import AllThoseRamseyClasses.Lifts.MinimalGeometricCutComponentPath
import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents
import Mathlib.Data.Fintype.EquivFin

/-!
# Explicit component indices for the weak-source multicomponent lift argument

The remaining Section 3 Claim 2 concerns how many DISTINCT source
Gaifman components of the right-exclusive region can appear in a
chosen mixed geometric piece. Path assertions alone obscure that
combinatorial parameter.

This module packages Gaifman reachability outside an exact vertex
cut S as a setoid of surviving source vertices. Its quotient is a
type of genuine components. When the original source is finite,
the component-index type is finite.

For an actual minimal cut R ⊆ S, if its selected left component
contains a right-exclusive vertex z, then z must have a DIFFERENT
component index in Source minus S from the right-exclusive vertex y
used to select the cut. In particular the right-exclusive source
region has at least two distinct components. No EHN injectivity or
function-fibre reflection is required for this observation.

This is a reusable structural invariant, not yet the full
multicomponent induction or the published Claim 2.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The exact Gaifman component equivalence on vertices OUTSIDE S.
Paths are taken in the original functional graph encoding with S
deleted: a component cannot pass through even one cut vertex. -/
def functionalOutsideComponentSetoid
    (A : Structure L V) (S : Set V) :
    Setoid {x : V // x ∉ S} where
  r := ReachOutside A.graph S
  iseqv := {
    refl := by
      intro x
      exact Relation.ReflTransGen.refl
    symm := by
      intro x y hxy
      exact reachOutside_symm A.graph S hxy
    trans := by
      intro x y z hxy hyz
      exact hxy.trans hyz
  }

/-- Genuine component identifiers after deleting exactly S. -/
abbrev FunctionalOutsideComponentId
    (A : Structure L V) (S : Set V) :=
  Quotient (functionalOutsideComponentSetoid A S)

/-- Label one surviving vertex by its exact path component. -/
def functionalOutsideComponentId
    (A : Structure L V) (S : Set V)
    (x : {v : V // v ∉ S}) :
    FunctionalOutsideComponentId A S :=
  Quotient.mk (functionalOutsideComponentSetoid A S) x

theorem functionalOutsideComponentId_eq_iff
    (A : Structure L V) (S : Set V)
    (x y : {v : V // v ∉ S}) :
    functionalOutsideComponentId A S x =
      functionalOutsideComponentId A S y ↔
    ReachOutside A.graph S x y := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- A finite source has only finitely many genuine Gaifman components
outside ANY vertex set (which need not itself be closed). -/
theorem finite_functionalOutsideComponentId
    [Finite V]
    (A : Structure L V) (S : Set V) :
    Finite (FunctionalOutsideComponentId A S) := by
  letI : Finite {v : V // v ∉ S} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Quotient.finite _

variable {H E F W U : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L W} {Source : Structure L U}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- Set of actual component indices occupied by right-exclusive
source vertices in the complement of the common-root preimage. -/
def weakRightExclusiveComponentIds
    (f : U → W) :
    Set (FunctionalOutsideComponentId Source
      (weakFreeRootPart (sL := sL) (iL := iL) f)) :=
  {c | ∃ (z : U) (hz : z ∈
      weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f),
    functionalOutsideComponentId Source
      (weakFreeRootPart (sL := sL) (iL := iL) f)
      ⟨z, hz.2⟩ = c}

/-- The selected minimal piece's wrong-side vertex is always
from a different right-exclusive source component than its
chosen right separating witness. A mixed piece therefore really
enters ANOTHER right component, not the original one. -/
theorem weakMixedPiece_rightComponentId_ne
    (f : U → W)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := sL) (iL := iL) f)
    (y : U)
    (hy : y ∈ weakFreeRightPart
      (sL := sL) (iL := iL) (iR := iR) f)
    (hRight : d.right.1 = y)
    (z : U)
    (hzComponent : z ∈ functionalComponentFrom
      Source (Set.range d.roots) d.left)
    (hzRight : z ∈ weakFreeRightPart
      (sL := sL) (iL := iL) (iR := iR) f) :
    functionalOutsideComponentId Source
      (weakFreeRootPart (sL := sL) (iL := iL) f)
      ⟨y, hy.2⟩ ≠
    functionalOutsideComponentId Source
      (weakFreeRootPart (sL := sL) (iL := iL) f)
      ⟨z, hzRight.2⟩ := by
  intro hSame
  have hPath :
      ReachOutside Source.graph
        (weakFreeRootPart (sL := sL) (iL := iL) f)
        ⟨y, hy.2⟩ ⟨z, hzRight.2⟩ :=
    (functionalOutsideComponentId_eq_iff Source
      (weakFreeRootPart (sL := sL) (iL := iL) f)
      ⟨y, hy.2⟩ ⟨z, hzRight.2⟩).mp hSame
  exact (minimalGeometricPiece_component_not_reachable_from_right
    Source d
    (weakFreeRootPart (sL := sL) (iL := iL) f)
    hRoots ⟨y, hy.2⟩ hRight
    hzComponent hzRight.2) hPath

/-- A genuinely mixed selected piece proves that the right-exclusive
part occupies at least TWO distinct Gaifman components of the
original source after deleting the complete common-root preimage.
This does not require any global injectivity or source finiteness. -/
theorem weakMixedPiece_twoDistinctRightComponents
    (f : U → W)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := sL) (iL := iL) f)
    (y : U)
    (hy : y ∈ weakFreeRightPart
      (sL := sL) (iL := iL) (iR := iR) f)
    (hRight : d.right.1 = y)
    (z : U)
    (hzComponent : z ∈ functionalComponentFrom
      Source (Set.range d.roots) d.left)
    (hzRight : z ∈ weakFreeRightPart
      (sL := sL) (iL := iL) (iR := iR) f) :
    ∃ c₁ c₂ : FunctionalOutsideComponentId Source
        (weakFreeRootPart (sL := sL) (iL := iL) f),
      c₁ ∈ weakRightExclusiveComponentIds
        (Source := Source) (sL := sL) (iL := iL)
        (iR := iR) f ∧
      c₂ ∈ weakRightExclusiveComponentIds
        (Source := Source) (sL := sL) (iL := iL)
        (iR := iR) f ∧
      c₁ ≠ c₂ := by
  let S : Set U := weakFreeRootPart (sL := sL) (iL := iL) f
  let c₁ : FunctionalOutsideComponentId Source S :=
    functionalOutsideComponentId Source S ⟨y, hy.2⟩
  let c₂ : FunctionalOutsideComponentId Source S :=
    functionalOutsideComponentId Source S ⟨z, hzRight.2⟩
  refine ⟨c₁, c₂, ?_, ?_, ?_⟩
  · exact ⟨y, hy, rfl⟩
  · exact ⟨z, hzRight, rfl⟩
  · exact weakMixedPiece_rightComponentId_ne
      f d hRoots y hy hRight z hzComponent hzRight

end AllThoseRamseyClasses.Lifts
