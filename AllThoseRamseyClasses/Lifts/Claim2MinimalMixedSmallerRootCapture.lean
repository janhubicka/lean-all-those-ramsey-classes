import AllThoseRamseyClasses.Lifts.RootRetentionLocalization

/-!
# Global smallest mixed source piece forces capture in a mixed smaller cut

The local positive-B-rank dichotomy can return a genuine smaller
positive minimal closed separator d with its full ordered root
inside the target seam, and two opposite-side source endpoints
in the old outer selected component. If d's selected nonroot
component is itself A/B-mixed, the existing finite global
MINIMAL-MIXED nonroot size hypothesis on the old outer piece P
forces d's component to capture an actual old P root vertex.

This is an explicit original-source certificate, not a theorem
that capture is impossible. It explains why trying to iterate
indefinitely through noncapturing smaller mixed pieces is the
wrong method when P has already been chosen globally minimal.
The source seam incursion must instead be analyzed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An ACTUAL smaller source-root piece which is itself mixed on the
same two prescribed exclusive source regions must capture an old
root of a globally smallest mixed original piece, provided both
of d's distinguished endpoints lie in the old selected component.

The witness belongs to the OLD root and original common seam,
is reached inside d's selected NONROOT component, and is not
one of d's own root vertices. Thus old-root retention fails. -/
theorem claim2_minimalMixed_smallerMixed_capturesOldRoot
    {V : Type} [Finite V]
    (Source : Structure L V)
    (S AOnly BOnly : Set V)
    (P : MixedGeometricPiece Source S AOnly BOnly)
    (hMinimal : ∀ Q : MixedGeometricPiece Source S AOnly BOnly,
      P.nonrootCount ≤ Q.nonrootCount)
    {m : ℕ} (d : GeometricFunctionalPieceData Source m)
    (hm : 0 < m)
    (hDrootSeam : Set.range d.roots ⊆ S)
    (hDleftOld :
      d.left.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hDrightOld :
      d.right.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hDA : ∃ a : V,
      a ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left ∧ a ∈ AOnly)
    (hDB : ∃ b : V,
      b ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left ∧ b ∈ BOnly) :
    ∃ r : V,
      r ∈ Set.range P.data.roots ∧
      r ∈ S ∧
      r ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left ∧
      r ∉ Set.range d.roots ∧
      ¬ Set.range P.data.roots ⊆ Set.range d.roots := by
  let Q : MixedGeometricPiece Source S AOnly BOnly := {
    width := m
    data := d
    positive := hm
    roots_in_common := hDrootSeam
    left_mixed := hDA
    right_mixed := hDB
  }
  obtain ⟨r, hrOld, hrCaptured⟩ :=
    minimalMixedPiece_otherMixed_capturesOldRoot
      Source S AOnly BOnly P Q hMinimal hDleftOld hDrightOld
  refine ⟨r, hrOld, P.roots_in_common hrOld, hrCaptured,
    hrCaptured.1, ?_⟩
  intro hRetained
  exact hrCaptured.1 (hRetained hrOld)

/-- Equivalently, among all genuinely A/B-mixed smaller-root pieces
with both endpoints in the selected component of a globally smallest
mixed outer P, none can avoid every OLD separator-root vertex.
This is the exact NO-CAPTURE obstruction to nested mixed descent. -/
theorem claim2_minimalMixed_no_noncapturing_smallerMixed
    {V : Type} [Finite V]
    (Source : Structure L V)
    (S AOnly BOnly : Set V)
    (P : MixedGeometricPiece Source S AOnly BOnly)
    (hMinimal : ∀ Q : MixedGeometricPiece Source S AOnly BOnly,
      P.nonrootCount ≤ Q.nonrootCount)
    {m : ℕ} (d : GeometricFunctionalPieceData Source m)
    (hm : 0 < m)
    (hDrootSeam : Set.range d.roots ⊆ S)
    (hDleftOld :
      d.left.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hDrightOld :
      d.right.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hNoCapture : ∀ r : V,
      r ∈ Set.range P.data.roots →
        r ∉ functionalComponentFrom Source
          (Set.range d.roots) d.left) :
    ¬ ((∃ a : V,
        a ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left ∧ a ∈ AOnly) ∧
       (∃ b : V,
        b ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left ∧ b ∈ BOnly)) := by
  intro hBoth
  obtain ⟨r, hrOld, _hrSeam, hrComp, _hrNew, _hLoss⟩ :=
    claim2_minimalMixed_smallerMixed_capturesOldRoot
      Source S AOnly BOnly P hMinimal d hm hDrootSeam
      hDleftOld hDrightOld hBoth.1 hBoth.2
  exact hNoCapture r hrOld hrComp

end AllThoseRamseyClasses.Lifts
