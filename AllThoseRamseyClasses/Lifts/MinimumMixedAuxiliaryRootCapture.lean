import AllThoseRamseyClasses.Lifts.GeneralOldRootSplitObstruction
import AllThoseRamseyClasses.Lifts.MinimalMixedGeometricPiece

/-!
# Minimum mixed-piece size forces one-sidedness or OLD-root capture

Let P be a genuinely smallest mixed source piece rooted inside the
common closed cut S, with old selected component C. Let Q be an
auxiliary positive-width minimal closed-separator source piece whose
whole root lies in S, both distinguished vertices lie inside C,
and Q.left is A-exclusive.

If Q.left's own component meets any B-exclusive vertex, then Q
is itself genuinely mixed. By minimum cardinality, its nonroot
component cannot be a STRICT subset of C. Yet it excludes Q.right,
which also belongs to C; therefore Q.left's component must ESCAPE C.

The already verified escaping-component/captured-old-root theorem
then supplies an actual vertex of the old root R(P) in Q.left.
If instead Q.left does not meet B, it is A-only. Thus EVERY
eligible auxiliary Q has the exact source-side dichotomy

  Q.left is A-only  OR  Q.left captures an old-root vertex.

The verified original-global Claim 1 excludes the A-only
alternative for an A-support-minimal witness when the target
images of Q's whole ordered root tuple are injective.

This statement is PURE source geometry, with no target EHN
quotient, invented forbidden-family premise or extra axiom.
It is a reusable missing link between #681's interior-cut
selection and #676's no-split localization.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- For a minimum genuine mixed piece P and an auxiliary
positive-width source chart Q rooted in S and spanning
two vertices of P's old selected component, the auxiliary
left component is EITHER B-free OR captures a vertex of the
old P-root.

The selected auxiliary left vertex must itself be A-only
to interpret the B-free alternative as a one-sided A-piece.
No minimality of forbidden weak-map support is required for
this SOURCE-only dichotomy. -/
theorem minimumMixed_auxiliaryLeft_oneSided_or_oldRootCapture
    [Finite V]
    (Source : Structure L V)
    (S AOnly BOnly : Set V)
    (P : MixedGeometricPiece Source S AOnly BOnly)
    (hMinP : ∀ D : MixedGeometricPiece Source S AOnly BOnly,
      P.nonrootCount ≤ D.nonrootCount)
    {m : ℕ}
    (Q : GeometricFunctionalPieceData Source m)
    (hm : 0 < m)
    (hQrootS : Set.range Q.roots ⊆ S)
    (hQleftOld : Q.left.1 ∈
      functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hQrightOld : Q.right.1 ∈
      functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hQleftA : Q.left.1 ∈ AOnly) :
    (∀ z : V,
      z ∈ functionalComponentFrom Source
        (Set.range Q.roots) Q.left →
      z ∉ BOnly) ∨
    ∃ r : V, r ∈ Set.range P.data.roots ∧
      r ∈ functionalComponentFrom Source
        (Set.range Q.roots) Q.left := by
  classical
  by_cases hB : ∃ z : V,
      z ∈ functionalComponentFrom Source
        (Set.range Q.roots) Q.left ∧ z ∈ BOnly
  · right
    let M : MixedGeometricPiece Source S AOnly BOnly := {
      width := m
      data := Q
      positive := hm
      roots_in_common := hQrootS
      left_mixed := ⟨Q.left.1,
        functionalComponentFrom_root Source
          (Set.range Q.roots) Q.left, hQleftA⟩
      right_mixed := hB
    }
    by_contra hNotCaptured
    have hQleftSubset :
        functionalComponentFrom Source
          (Set.range Q.roots) Q.left ⊆
        functionalComponentFrom Source
          (Set.range P.data.roots) P.data.left := by
      by_contra hEscapes
      exact hNotCaptured
        (geometricPiece_escapingComponent_capturesOldRoot
          Source P.data Q hQleftOld hEscapes)
    have hQrightNotLeft :
        Q.right.1 ∉ functionalComponentFrom Source
          (Set.range Q.roots) Q.left := by
      intro hRightInLeft
      exact Q.minimal.2.1 hRightInLeft.2
    have hProper :
        functionalComponentFrom Source
          (Set.range Q.roots) Q.left ⊂
        functionalComponentFrom Source
          (Set.range P.data.roots) P.data.left := by
      apply Set.ssubset_iff_subset_ne.mpr
      refine ⟨hQleftSubset, ?_⟩
      intro heq
      apply hQrightNotLeft
      rw [heq]
      exact hQrightOld
    exact minimalMixedGeometricPiece_no_proper_mixed_component
      P hMinP M hProper
  · left
    intro z hz hzB
    exact hB ⟨z, hz, hzB⟩

end AllThoseRamseyClasses.Lifts
