import AllThoseRamseyClasses.Lifts.GeometricFunctionalPieces

/-!
# Two-sided capture requires two distinct old root SOURCE indices

A genuine smaller minimal closed separator d can capture source
vertices of the old outer piece's closed separator root P
in both its selected d.left component and its OPPOSITE d.right
component. By the actual Gaifman component disjointness,
these must be DIFFERENT old root vertices, hence arise
at distinct indices of the complete P.roots enumeration.

In particular, an old geometric piece of root width ONE can
never exhibit simultaneous left- and right-component capture.

This is an intrinsic original-source geometric obstruction
certificate. It uses neither an EHN target map nor a
canonical-lift/minimality hypothesis. It does not exclude
two-sided capture for larger old roots.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Simultaneous capture of old P-root SOURCE vertices in two
different components of the SAME genuine smaller separator
produces TWO DISTINCT positions in P's original ordered root,
with their actual SOURCE component memberships. -/
theorem claim2_twoSidedOldRootCapture_distinctIndices
    {V : Type}
    (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (d : GeometricFunctionalPieceData Source m)
    (hLeftCapture :
      ∃ r : V, r ∈ Set.range P.roots ∧
        r ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left)
    (hRightCapture :
      ∃ s : V, s ∈ Set.range P.roots ∧
        s ∈ functionalComponentFrom Source
          (Set.range d.roots) d.right) :
    ∃ i j : Fin n,
      i ≠ j ∧
      P.roots i ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left ∧
      P.roots j ∈ functionalComponentFrom Source
        (Set.range d.roots) d.right := by
  obtain ⟨r, ⟨i, hi⟩, hrLeft⟩ := hLeftCapture
  obtain ⟨s, ⟨j, hj⟩, hsRight⟩ := hRightCapture
  have hij : i ≠ j := by
    intro hEq
    have hrs : r = s := by
      calc
        r = P.roots i := hi.symm
        _ = P.roots j := congrArg P.roots hEq
        _ = s := hj
    have hrRight : r ∈ functionalComponentFrom Source
        (Set.range d.roots) d.right := by
      simpa only [hrs] using hsRight
    exact (Set.disjoint_left.mp
      (geometricPiece_components_disjoint Source d)) hrLeft hrRight
  refine ⟨i, j, hij, ?_, ?_⟩
  · simpa only [hi] using hrLeft
  · simpa only [hj] using hsRight

/-- With only ONE old ordered source root vertex, the two
opposite components of a true smaller separator cannot both
capture old-root vertices. This is a genuine width-one
obstruction result, not a property of weak target images. -/
theorem claim2_widthOne_no_twoSidedOldRootCapture
    {V : Type}
    (Source : Structure L V)
    {m : ℕ}
    (P : GeometricFunctionalPieceData Source 1)
    (d : GeometricFunctionalPieceData Source m)
    (hLeftCapture :
      ∃ r : V, r ∈ Set.range P.roots ∧
        r ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left)
    (hRightCapture :
      ∃ s : V, s ∈ Set.range P.roots ∧
        s ∈ functionalComponentFrom Source
          (Set.range d.roots) d.right) : False := by
  obtain ⟨i, j, hij, _hiLeft, _hjRight⟩ :=
    claim2_twoSidedOldRootCapture_distinctIndices
      Source P d hLeftCapture hRightCapture
  exact hij (Subsingleton.elim i j)

end AllThoseRamseyClasses.Lifts
