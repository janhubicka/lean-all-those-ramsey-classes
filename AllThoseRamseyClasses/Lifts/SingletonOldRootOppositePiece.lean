import AllThoseRamseyClasses.Lifts.RootRetentionLocalization
import AllThoseRamseyClasses.Lifts.MinimalMixedGeometricPiece

/-!
# Singleton old roots force the OPPOSITE piece to be a proper one-sided sub-piece

The original Section 3 Claim 2 chooses a genuinely mixed
source piece P with the least possible number of nonroot
vertices. Suppose its old separating root consists of at
most ONE vertex. Let Q be another genuine geometric piece
whose two distinguished vertices lie in P's selected
component, while its LEFT component captures the old
separator-root vertex.

The previously verified path/capture theorem gives a simple
dichotomy: if Q's RIGHT component could leave P's selected
component, it would have to capture an old root vertex as
well. The singleton assumption makes that the SAME vertex
already captured by Q's LEFT component, contradicting
disjointness of the two components.

Thus Q's opposite/right component is contained in P's
selected component. It is a STRICT subset because the
original Q.left vertex belongs to P but cannot belong to
Q.right's component. Minimum mixed nonroot size then
forces this opposite component to contain NO left-exclusive
source vertex whenever Q.right is right-exclusive.

So, for singleton old roots, the source geometry itself
supplies a genuine, strictly smaller, one-sided geometric
sub-piece on the RIGHT of Q. A full canonical-lift flip
still requires injective target images on Q's new root.
No free-amalgam target map or forbidden-image quotient is
assumed in this pure source lemma.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Suppose P is a smallest genuine mixed geometric source
piece and its OLD root has at most one original vertex.

For any genuine geometric piece Q with both selected
distinguished source vertices in P's old nonroot component,
if Q's LEFT component captures an old P-root vertex and
its RIGHT distinguished vertex is right-exclusive, then
Q's OPPOSITE (right) component is a STRICT subcomponent
of P's selected component and has NO left-exclusive vertex.

The right-rooted orientation of Q is itself a genuine
minimal closed-separator piece. No global weak-map
injectivity or existence of a new forbidden source is used. -/
theorem minimalMixedSingletonOldRoot_oppositeComponent_oneSided
    [Finite V]
    (Source : Structure L V)
    (S AOnly BOnly : Set V)
    (P : MixedGeometricPiece Source S AOnly BOnly)
    (hMinP : ∀ D : MixedGeometricPiece Source S AOnly BOnly,
      P.nonrootCount ≤ D.nonrootCount)
    (hSingletonOldRoot :
      ∀ a b : V,
        a ∈ Set.range P.data.roots →
        b ∈ Set.range P.data.roots → a = b)
    {m : ℕ}
    (Q : GeometricFunctionalPieceData Source m)
    (hQpositive : 0 < m)
    (hQrootS : Set.range Q.roots ⊆ S)
    (hQleftOld :
      Q.left.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hQrightOld :
      Q.right.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hQrightB : Q.right.1 ∈ BOnly)
    (hCaptured : ∃ r : V,
      r ∈ Set.range P.data.roots ∧
      r ∈ functionalComponentFrom Source
        (Set.range Q.roots) Q.left) :
    functionalComponentFrom Source (Set.range Q.roots) Q.right ⊂
        functionalComponentFrom Source
          (Set.range P.data.roots) P.data.left ∧
      ∀ z : V,
        z ∈ functionalComponentFrom Source
          (Set.range Q.roots) Q.right →
        z ∉ AOnly := by
  let Qswap : GeometricFunctionalPieceData Source m := {
    roots := Q.roots
    roots_injective := Q.roots_injective
    left := Q.right
    right := Q.left
    minimal := minimalClosedSeparator_swap
      Source (Set.range Q.roots) Q.left Q.right Q.minimal
  }
  have hRightSubset :
      functionalComponentFrom Source (Set.range Q.roots) Q.right ⊆
        functionalComponentFrom Source
          (Set.range P.data.roots) P.data.left := by
    by_contra hEscape
    have hEscapeSwap :
        ¬ functionalComponentFrom Source
            (Set.range Qswap.roots) Qswap.left ⊆
          functionalComponentFrom Source
            (Set.range P.data.roots) P.data.left := hEscape
    obtain ⟨rEscape, hrEscapeOld, hrEscapeRight⟩ :=
      geometricPiece_escapingComponent_capturesOldRoot
        Source P.data Qswap hQrightOld hEscapeSwap
    obtain ⟨rLeft, hrLeftOld, hrLeftInQ⟩ := hCaptured
    have hSameRoot : rEscape = rLeft :=
      hSingletonOldRoot rEscape rLeft hrEscapeOld hrLeftOld
    have hrRight :
        rLeft ∈ functionalComponentFrom Source
          (Set.range Q.roots) Q.right := by
      change rEscape ∈ functionalComponentFrom Source
        (Set.range Q.roots) Q.right at hrEscapeRight
      rw [hSameRoot] at hrEscapeRight
      exact hrEscapeRight
    have hDisjoint :=
      geometricPiece_components_disjoint Source Q
    exact (Set.disjoint_left.mp hDisjoint) hrLeftInQ hrRight
  have hLeftNotRight :
      Q.left.1 ∉ functionalComponentFrom Source
        (Set.range Q.roots) Q.right := by
    intro hLeftInRight
    have hInLeft :=
      functionalComponentFrom_root Source
        (Set.range Q.roots) Q.left
    exact (Set.disjoint_left.mp
      (geometricPiece_components_disjoint Source Q))
      hInLeft hLeftInRight
  have hRightProper :
      functionalComponentFrom Source (Set.range Q.roots) Q.right ⊂
        functionalComponentFrom Source
          (Set.range P.data.roots) P.data.left := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hRightSubset, ?_⟩
    intro hEq
    apply hLeftNotRight
    rw [hEq]
    exact hQleftOld
  have hNoLeft :
      ∀ z : V,
        z ∈ functionalComponentFrom Source
          (Set.range Q.roots) Q.right →
        z ∉ AOnly := by
    intro z hzRight hzA
    let M : MixedGeometricPiece Source S AOnly BOnly := {
      width := m
      data := Qswap
      positive := hQpositive
      roots_in_common := hQrootS
      left_mixed := ⟨z, hzRight, hzA⟩
      right_mixed := ⟨Q.right.1,
        functionalComponentFrom_root Source
          (Set.range Q.roots) Q.right, hQrightB⟩
    }
    exact minimalMixedGeometricPiece_no_proper_mixed_component
      P hMinP M hRightProper
  exact ⟨hRightProper, hNoLeft⟩

end AllThoseRamseyClasses.Lifts
