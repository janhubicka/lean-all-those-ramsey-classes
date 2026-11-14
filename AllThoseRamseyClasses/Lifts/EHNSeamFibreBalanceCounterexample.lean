import Mathlib.Tactic

/-!
# Track D: finite source-seam fibre balance counterexample

This is an exact combinatorial regression for the ORIGINAL source
seam-collision secondary minimization. A target seam point unused
by a selected two-root tuple need NOT be unused by all original
source vertices. Moving one collapsed source root to that already
occupied seam point may make its ROOT images injective while leaving
the GLOBAL number of ordered distinct-source collision pairs unchanged.

No structure, forbidden family, EHN embedding, canonical lift or
unrestricted original Claim 1/Claim 2 is asserted by this finite
coordinate example. The native local EHN checks remain separate.
-/

namespace AllThoseRamseyClasses.Lifts

/-- Three original vertices mapping to a two-point common seam:
the first two source coordinates collide, but both seam points
are already occupied by some original source vertex. -/
private def fibreOld : Fin 3 → Fin 2 :=
  fun i => if i = 0 then 0 else if i = 1 then 0 else 1

/-- Split the two selected source roots by recolouring coordinate 0
to the OTHER seam point, already occupied by original vertex 2. -/
private def fibreNew : Fin 3 → Fin 2 :=
  fun i => if i = 0 then 1 else fibreOld i

/-- Ordered distinct-source collision pairs for a finite seam which
contains ALL target points in this regression. -/
private def finiteSourceCollisionPairs (f : Fin 3 → Fin 2) :
    Finset (Fin 3 × Fin 3) :=
  Finset.univ.filter (fun p =>
    p.1 ≠ p.2 ∧ f p.1 = f p.2)

/-- Root-width 2 fits into a seam of size 2, and the root image
omits a seam point, but the FULL source image saturates the seam.
The proposed split separates the selected root coordinates. -/
theorem seamFibre_rootVacancy_notGlobalVacancy :
    fibreOld 0 = fibreOld 1 ∧
    fibreOld 0 ≠ fibreOld 2 ∧
    fibreNew 0 ≠ fibreNew 1 ∧
    (∀ t : Fin 2, ∃ x : Fin 3, fibreOld x = t) := by
  decide

/-- Nonetheless the candidate split has EXACTLY the same number
of global ordered original-source seam collision pairs (two).
Thus root injection alone does not yield strict secondary descent. -/
theorem seamFibre_splitCanPreserveGlobalCollisionCount :
    (finiteSourceCollisionPairs fibreOld).card = 2 ∧
    (finiteSourceCollisionPairs fibreNew).card = 2 := by
  decide

/-- GENERAL native-source coordinate fact: a one-vertex change leaves
all ordered collision pairs avoiding that original vertex untouched.
This is the unaffected-pairs half of the fibre-count formula. -/
theorem seamFibre_oneVertexRecolor_preserves_awayPairs
    {V UT : Type} [DecidableEq V]
    (f : V → UT) (Seam : Set UT)
    (a : V) (t : UT)
    (u v : V) (hu : u ≠ a) (hv : v ≠ a) :
    (u ≠ v ∧
      (if u = a then t else f u) =
        (if v = a then t else f v) ∧
      (if u = a then t else f u) ∈ Seam) ↔
    (u ≠ v ∧ f u = f v ∧ f u ∈ Seam) := by
  simp [hu, hv]

/-- GENERAL native-source coordinate fact: after a one-vertex move,
the new collisions incident with the changed vertex are exactly
its OTHER destination-fibre vertices, with no EHN assertion. -/
theorem seamFibre_oneVertexRecolor_incidentPair_iff_destinationFibre
    {V UT : Type} [DecidableEq V]
    (f : V → UT) (a : V) (t : UT)
    (u : V) (hu : u ≠ a) :
    ((if a = a then t else f a) =
      (if u = a then t else f u)) ↔ f u = t := by
  simp [hu, eq_comm]

/-- Stronger FINITE regression: with three original source vertices
mapped into a two-point common seam, EVERY possible source-wide
recolouring (not merely a one-point move) has at least two ORDERED
collision pairs. Thus the old map already minimizes the global
secondary collision count over all maps to that seam, even though
its selected two-root image is noninjective. No EHN claim. -/
theorem seamFibre_anyFullSeamMap_hasAtLeastTwoOrderedCollisions :
    ∀ g : Fin 3 → Fin 2,
      2 ≤ (finiteSourceCollisionPairs g).card := by
  decide

end AllThoseRamseyClasses.Lifts
