import AllThoseRamseyClasses.Lifts.GeometricInnerRootOuterBoundary
import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram

/-!
# The older opposite exterior of a nested geometric source flip is private

In an actual forbidden source A, let U be the complete native
generated root of one inner geometric piece d. Let T be an older
geometric minimal closed separator with components C and E,
and suppose the COMPLETE inner chosen component D sits in C.

The verified generated-root attachment lemma implies
  U minus T subset C
even when U and T are incomparable. Because E is a genuinely
DIFFERENT T-component, it meets neither C nor T, and hence
cannot meet U at all. Moreover D subset C, so E misses D.

Thus every vertex of the old outer OPPOSITE exterior E is
simultaneously private to the inner full gluing root and
belongs to the unchanged full functional complement of D.
This is the missing source-geometric reason the older
opposite exterior survives a selected inner Q flip.

The proof is genuinely in the original source; it neither
identifies weak EHN target-map vertices nor substitutes graph
adjacency for native function-generated closure.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V : Type}

/-- A genuine older opposite exterior component of a selected
minimal closed separator avoids the entire root AND the
entire private component of any nested inner piece whose
chosen component lies on the other older side.

There is no inclusion assumption between the two closed cuts.
The conclusion is exactly the privacy condition needed
to identify the exterior inside the retained full complement. -/
theorem nestedGeometric_outerExterior_avoids_innerPiece
    (A : Structure L V)
    {n m : ℕ}
    (inner : GeometricFunctionalPieceData A n)
    (outer : GeometricFunctionalPieceData A m)
    (hInnerInOuter :
      componentFrom A.graph (Set.range inner.roots) inner.left ⊆
        componentFrom A.graph (Set.range outer.roots) outer.left)
    (z : V)
    (hzExterior :
      z ∈ componentFrom A.graph (Set.range outer.roots) outer.right) :
    z ∉ Set.range inner.roots ∧
      z ∉ componentFrom A.graph (Set.range inner.roots) inner.left := by
  let U : Set V := Set.range inner.roots
  let T : Set V := Set.range outer.roots
  let C : Set V := componentFrom A.graph T outer.left
  let E : Set V := componentFrom A.graph T outer.right
  let D : Set V := componentFrom A.graph U inner.left
  have hDistinct : Disjoint C E :=
    geometricPiece_components_disjoint A outer
  have hRootAttached : U \ T ⊆ C :=
    generatedInnerRoot_outsideClosedOuterCut_attaches
      A T outer.minimal.1 outer.left D U
      hInnerInOuter (geometricPiece_left_boundary_closure A inner)
  constructor
  · intro hzU
    have hzNotT : z ∉ T := hzExterior.1
    have hzC : z ∈ C :=
      hRootAttached ⟨hzU, hzNotT⟩
    exact (Set.disjoint_left.mp hDistinct) hzC hzExterior
  · intro hzD
    have hzC : z ∈ C := hInnerInOuter hzD
    exact (Set.disjoint_left.mp hDistinct) hzC hzExterior

end AllThoseRamseyClasses.Lifts
