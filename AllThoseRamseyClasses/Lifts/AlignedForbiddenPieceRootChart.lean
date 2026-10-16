import AllThoseRamseyClasses.Lifts.FunctionalRootedIsoEmbedding
import AllThoseRamseyClasses.Lifts.GeometricPieceRootChart

/-!
# Normalize a rooted-isomorphic forbidden piece into the exact root chart

The original piece has an ordered tuple of root vertices enumerating
an exact closed cut R of a forbidden source A. A second rooted pattern
P, known to be fully root-isomorphic to that geometric piece, becomes
a full root extension of the SAME induced functional root A.induce R.

The conversion uses the verified full functional embedding obtained
from the ROOT-PRESERVING graph isomorphism. It retains the original
function domains and fibres, and sends the i-th root of the original
source to the i-th root of P.

This is the chart normalization required for the published flip:
if a weak target realization of P agrees with the old map at every
ordered root coordinate, it agrees on EVERY element of the full root
structure. The condition is purely an equality of vertex maps,
NOT an unjustified claim that a weak map is an induced embedding.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V UT : Type v}

/-- A rooted-isomorphic copy of an actual geometric minimal-cut
piece, represented as an extension of the ORIGINAL full functional
root structure, without any identification of carriers. -/
def alignedFunctionalRootExtension
    (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n)
    (P : FunctionalRootedPattern.{u,v} L n)
    (e : FunctionalRootedPatternIso P
      (geometricFunctionalRootedPattern A d)) :
    FunctionalRootExtension
      (closedCutRoot A (Set.range d.roots) d.minimal.1) where
  Carrier := P.Carrier
  str := P.str
  rootEmbedding :=
    (FunctionalRootedPatternIso.toFullEmbedding
        (P := geometricFunctionalRootedPattern A d)
        (Q := P) e.symm).comp
      (componentRootToPiece A (Set.range d.roots)
        d.minimal.1 d.left)

/-- The aligned root extension really sends the i-th original
root vertex to the i-th rooted vertex of P. -/
theorem alignedFunctionalRootExtension_root
    (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n)
    (P : FunctionalRootedPattern.{u,v} L n)
    (e : FunctionalRootedPatternIso P
      (geometricFunctionalRootedPattern A d))
    (i : Fin n) :
    (alignedFunctionalRootExtension A d P e).rootEmbedding
        (⟨d.roots i, ⟨i, rfl⟩⟩ : Set.range d.roots) =
      P.root i := by
  change e.symm.equiv ((geometricFunctionalRootedPattern A d).root i) =
    P.root i
  exact e.symm.roots i

/-- Equality of weak target maps on the ORDERED root tuple becomes
equality on EVERY vertex of the full induced functional root chart.
No injectivity of the weak maps is used in this step. -/
theorem alignedFunctionalRootExtension_rootMap
    (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n)
    (P : FunctionalRootedPattern.{u,v} L n)
    (e : FunctionalRootedPatternIso P
      (geometricFunctionalRootedPattern A d))
    (f : V → UT) (g : P.Carrier → UT)
    (hagrees : ∀ i : Fin n, g (P.root i) = f (d.roots i)) :
    ∀ r : Set.range d.roots,
      g ((alignedFunctionalRootExtension A d P e).rootEmbedding r) =
        f r.1 := by
  intro r
  obtain ⟨i, hi⟩ := r.property
  have hr : r =
      (⟨d.roots i, ⟨i, rfl⟩⟩ : Set.range d.roots) := by
    apply Subtype.ext
    exact hi.symm
  rw [hr, alignedFunctionalRootExtension_root]
  exact hagrees i

end AllThoseRamseyClasses.Lifts
