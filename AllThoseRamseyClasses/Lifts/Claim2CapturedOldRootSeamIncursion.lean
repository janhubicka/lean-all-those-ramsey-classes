import AllThoseRamseyClasses.Lifts.RootRetentionLocalization

/-!
# Captured old roots give literal seam-incursion paths in the smaller piece

The original 2019 Claim 2 smaller-root alternative may produce a
genuine minimal closed separator d whose selected B-side component
captures an old outer root vertex of P. This is not excluded by
injectivity on B-component generated boundaries (and can occur even
when the entire weak map is injective).

The key actual SOURCE certificate is stronger than a bare failure
of nested-piece inclusion: a captured old root belongs to the
selected d-component AFTER DELETING the entire new closed root, so
there is a genuine Gaifman path from d.left to this old root avoiding
d's complete root. Its image still lies in the full TARGET seam.

Thus capture entails both strict LOSS of old-root retention and a
nonempty seam incursion into the new selected component. The exact
right next problem is to control such source seam-incursion paths;
not to infer their absence from target-map injectivity.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An old separator root captured by the selected nonroot component
of a smaller true geometric piece cannot occur in the smaller root
itself. In particular the OLD root is not retained by the NEW cut.
No function arity, weak target map or forbidden-family assumption. -/
theorem claim2_capturedOldRoot_forces_rootLoss
    {V : Type} (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (d : GeometricFunctionalPieceData Source m)
    (hCapture : ∃ r : V, r ∈ Set.range P.roots ∧
      r ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left) :
    ¬ Set.range P.roots ⊆ Set.range d.roots := by
  rintro hRetained
  obtain ⟨r, hrOld, hrCaptured⟩ := hCapture
  exact hrCaptured.1 (hRetained hrOld)

/-- A captured old-root vertex is reached by an ACTUAL SOURCE
Gaifman path from the selected d.left vertex avoiding every vertex
of the COMPLETE new root. Its OLD target value lies in the common
target seam, while the vertex itself is NOT in d's new root.

This is a literal source-path obstruction, not a quotient of the
weak target image or an assumption that the smaller piece is nested. -/
theorem claim2_capturedOldRoot_has_seamIncursionPath
    {V UT : Type} (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (d : GeometricFunctionalPieceData Source m)
    (f : V → UT) (Seam : Set UT)
    (hOldRootSeam : ∀ i : Fin n, f (P.roots i) ∈ Seam)
    (hCapture : ∃ r : V, r ∈ Set.range P.roots ∧
      r ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left) :
    ∃ (i : Fin n) (hi : P.roots i ∉ Set.range d.roots),
      f (P.roots i) ∈ Seam ∧
      ReachOutside Source.graph (Set.range d.roots) d.left
        (⟨P.roots i, hi⟩ :
          {z : V // z ∉ Set.range d.roots}) ∧
      ¬ Set.range P.roots ⊆ Set.range d.roots := by
  obtain ⟨r, ⟨i, rfl⟩, hrCaptured⟩ := hCapture
  refine ⟨i, hrCaptured.1, hOldRootSeam i, hrCaptured.2, ?_⟩
  exact claim2_capturedOldRoot_forces_rootLoss
    Source P d ⟨P.roots i, ⟨i, rfl⟩, hrCaptured⟩

/-- The precise sufficient condition that DOES exclude old-root
capture: the entire selected smaller component avoids the full
TARGET seam. This is strictly stronger than injectivity on a
generated boundary; it is not automatic for a weak EHN map. -/
theorem claim2_noCapture_of_selectedComponent_avoids_seam
    {V UT : Type} (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (d : GeometricFunctionalPieceData Source m)
    (f : V → UT) (Seam : Set UT)
    (hOldRootSeam : ∀ i : Fin n, f (P.roots i) ∈ Seam)
    (hNoSeamInNewComponent : ∀ z : V,
      z ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left → f z ∉ Seam) :
    ∀ r : V, r ∈ Set.range P.roots →
      r ∉ functionalComponentFrom Source
        (Set.range d.roots) d.left := by
  intro r hrOld hrCaptured
  obtain ⟨i, hi⟩ := hrOld
  apply hNoSeamInNewComponent r hrCaptured
  simpa only [hi] using hOldRootSeam i

end AllThoseRamseyClasses.Lifts
