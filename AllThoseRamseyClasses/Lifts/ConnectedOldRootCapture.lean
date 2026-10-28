import AllThoseRamseyClasses.Lifts.GeneralOldRootCapturedRightPiece

/-!
# Avoiding old-root splitting when its vertices remain connected

The general-width Claim 2 obstruction of the original 2019
lift is now precisely isolated: a new separating piece Q
may put DISTINCT vertices of the old mixed piece root R
in two opposite components after deleting Q's root U.
In that situation the converse B-only proper sub-piece need
not be localized inside the original mixed piece.

This module extracts a structural sufficient condition for
the positive general-width side. If R is disjoint from U
and all vertices of R remain connected to each other in
the actual source Gaifman graph AFTER deleting U, then
capture of ONE R-vertex by Q.left forces capture of ALL R.
The previously verified arbitrary-width capture theorem
then gives a genuine proper opposite B-only sub-piece at
minimum mixed nonroot cardinality.

A concrete convenient case is a source Gaifman CLIQUE root
R disjoint from U. This condition is stronger than ordinary
root irreducibility in some functional languages and is not
claimed for arbitrary minimal separating roots. It does not
remove the genuine multi-root split obstruction in general.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- If every vertex of the old separating root survives the
new root deletion and the old-root vertices are pairwise
reachable outside the new root, then one captured old root
forces the ENTIRE old root into the same new component. -/
theorem geometricOldRoot_capturedAll_of_connectedOutsideNewRoot
    (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (Q : GeometricFunctionalPieceData Source m)
    (hAvoid : Set.range P.roots ⊆
      {x : V | x ∉ Set.range Q.roots})
    (hConnected : ∀ a b : V,
      (ha : a ∈ Set.range P.roots) →
      (hb : b ∈ Set.range P.roots) →
      ReachOutside Source.graph (Set.range Q.roots)
        ⟨a, hAvoid ha⟩ ⟨b, hAvoid hb⟩)
    (hCapturedLeft : ∃ r : V,
      r ∈ Set.range P.roots ∧
      r ∈ functionalComponentFrom Source
        (Set.range Q.roots) Q.left) :
    Set.range P.roots ⊆
      functionalComponentFrom Source
        (Set.range Q.roots) Q.left := by
  obtain ⟨r, hr, hrLeft⟩ := hCapturedLeft
  intro z hz
  have hPath :
      ReachOutside Source.graph (Set.range Q.roots)
        Q.left ⟨z, hAvoid hz⟩ := by
    exact hrLeft.2.trans (hConnected r z hr hz)
  exact ⟨hAvoid hz, hPath⟩

/-- A Gaifman-clique old root disjoint from the new separator
cannot SPLIT into different new components: any one captured
old-root vertex forces all of them into its component.

This is a concrete arbitrary-width refinement of the
verified singleton-root argument; no finite cardinality,
forbidden family or target weak map is required. -/
theorem geometricOldRoot_capturedAll_of_cliqueDisjoint
    (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (Q : GeometricFunctionalPieceData Source m)
    (hAvoid : Set.range P.roots ⊆
      {x : V | x ∉ Set.range Q.roots})
    (hClique : ∀ a b : V,
      a ∈ Set.range P.roots →
      b ∈ Set.range P.roots →
      a ≠ b → GaifmanAdjacent Source.graph a b)
    (hCapturedLeft : ∃ r : V,
      r ∈ Set.range P.roots ∧
      r ∈ functionalComponentFrom Source
        (Set.range Q.roots) Q.left) :
    Set.range P.roots ⊆
      functionalComponentFrom Source
        (Set.range Q.roots) Q.left := by
  apply geometricOldRoot_capturedAll_of_connectedOutsideNewRoot
    Source P Q hAvoid
  · intro a b ha hb
    by_cases hab : a = b
    · subst b
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single
        (hClique a b ha hb hab)
  · exact hCapturedLeft

/-- For a MINIMUM genuine mixed old source piece with a
Gaifman-clique old root that is disjoint from the new separator,
capture of one old root vertex is already enough for the complete
arbitrary-width B-only opposite proper sub-piece conclusion.

This directly invokes the certified general-width theorem with
its previously OPEN all-old-roots-captured premise now proved
from a transparent SOURCE graph condition. -/
theorem minimalMixedCliqueOldRoot_oppositeComponent_oneSided
    [Finite V]
    (Source : Structure L V)
    (S AOnly BOnly : Set V)
    (P : MixedGeometricPiece Source S AOnly BOnly)
    (hMinP : ∀ D : MixedGeometricPiece Source S AOnly BOnly,
      P.nonrootCount ≤ D.nonrootCount)
    {m : ℕ}
    (Q : GeometricFunctionalPieceData Source m)
    (hQpositive : 0 < m)
    (hAvoid : Set.range P.data.roots ⊆
      {x : V | x ∉ Set.range Q.roots})
    (hClique : ∀ a b : V,
      a ∈ Set.range P.data.roots →
      b ∈ Set.range P.data.roots →
      a ≠ b → GaifmanAdjacent Source.graph a b)
    (hCapturedLeft : ∃ r : V,
      r ∈ Set.range P.data.roots ∧
      r ∈ functionalComponentFrom Source
        (Set.range Q.roots) Q.left)
    (hQrootS : Set.range Q.roots ⊆ S)
    (hQrootInsideP :
      Set.range Q.roots ⊆ geometricPieceVertices Source P.data)
    (hQleftOld :
      Q.left.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hQrightOld :
      Q.right.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hQrightB : Q.right.1 ∈ BOnly) :
    (Set.range Q.roots ∪
      functionalComponentFrom Source (Set.range Q.roots) Q.right) ⊂
      geometricPieceVertices Source P.data ∧
    functionalComponentFrom Source (Set.range Q.roots) Q.right ⊂
      functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left ∧
    ∀ z : V,
      z ∈ functionalComponentFrom Source
        (Set.range Q.roots) Q.right → z ∉ AOnly := by
  have hCapturedAll :
      Set.range P.data.roots ⊆
        functionalComponentFrom Source
          (Set.range Q.roots) Q.left :=
    geometricOldRoot_capturedAll_of_cliqueDisjoint
      Source P.data Q hAvoid hClique hCapturedLeft
  exact minimalMixedCapturedEntireOldRoot_oppositeComponent_oneSided
    Source S AOnly BOnly P hMinP Q hQpositive
    hCapturedAll hQrootS hQrootInsideP
    hQleftOld hQrightOld hQrightB

end AllThoseRamseyClasses.Lifts
