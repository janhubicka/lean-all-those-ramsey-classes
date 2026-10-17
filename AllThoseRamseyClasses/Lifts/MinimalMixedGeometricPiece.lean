import AllThoseRamseyClasses.Lifts.GeometricFunctionalPieces
import Mathlib.Data.Set.Card

/-!
# Choosing a smallest genuinely mixed geometric forbidden-source piece

The 2019 Section 3 strong-amalgamation argument chooses a
geometrically genuine rooted piece with the smallest number
of NON-ROOT source vertices among all those rooted inside the
common-root preimage and meeting BOTH exclusive side regions.

This construction is valid for a FINITE original source without
assuming injectivity of any map to the target. The chosen piece
is an actual minimal FUNCTION-CLOSED separating-cut piece, not
an arbitrary rooted substructure or a weak image quotient.

This module isolates the exact finite selection as a general
lemma. Existence of an eligible mixed piece and the geometric
contradiction based on a smaller subpiece are separate tasks.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- An ACTUAL positive-width minimal-closed-separator piece of
a finite source, whose entire ordered root lies in S and whose
selected non-root Gaifman component contains at least one
vertex from each of two prescribed regions.

No source-to-target map is part of this definition: its image
partition is represented by the literal sets AOnly, BOnly. -/
structure MixedGeometricPiece
    (Source : Structure L V)
    (S AOnly BOnly : Set V) where
  width : ℕ
  data : GeometricFunctionalPieceData Source width
  positive : 0 < width
  roots_in_common : Set.range data.roots ⊆ S
  left_mixed : ∃ a : V,
    a ∈ functionalComponentFrom Source
      (Set.range data.roots) data.left ∧ a ∈ AOnly
  right_mixed : ∃ b : V,
    b ∈ functionalComponentFrom Source
      (Set.range data.roots) data.left ∧ b ∈ BOnly

/-- The number of genuine NONROOT source vertices in the
selected component. For finite carriers this is the
actual finite count used in the manuscript's Claim 2. -/
noncomputable def MixedGeometricPiece.nonrootCount
    {Source : Structure L V} {S AOnly BOnly : Set V}
    (P : MixedGeometricPiece Source S AOnly BOnly) : ℕ :=
  (functionalComponentFrom Source
    (Set.range P.data.roots) P.data.left).ncard

/-- If a finite source has ANY genuine positive-width mixed
piece rooted inside S, it has one with the SMALLEST actual
number of nonroot vertices. No injective normalization of
the source map is used. -/
theorem exists_minimalMixedGeometricPiece
    [Finite V]
    (Source : Structure L V)
    (S AOnly BOnly : Set V)
    (hExists : Nonempty
      (MixedGeometricPiece Source S AOnly BOnly)) :
    ∃ P : MixedGeometricPiece Source S AOnly BOnly,
      ∀ Q : MixedGeometricPiece Source S AOnly BOnly,
        P.nonrootCount ≤ Q.nonrootCount := by
  classical
  let counts : Set ℕ :=
    {k | ∃ P : MixedGeometricPiece Source S AOnly BOnly,
      P.nonrootCount = k}
  have hNonempty : counts.Nonempty := by
    obtain ⟨P⟩ := hExists
    exact ⟨P.nonrootCount, P, rfl⟩
  have hLeast : sInf counts ∈ counts :=
    Nat.sInf_mem hNonempty
  obtain ⟨P, hCard⟩ := hLeast
  refine ⟨P, ?_⟩
  intro Q
  rw [hCard]
  exact Nat.sInf_le (show Q.nonrootCount ∈ counts from
    ⟨Q, rfl⟩)

/-- A size-minimal genuinely mixed piece cannot have any
OTHER genuine positive-width mixed piece with strictly
fewer non-root source vertices. This is the exact
minimality premise needed for the next multi-component
proper-subpiece argument, not that argument itself. -/
theorem minimalMixedGeometricPiece_no_strictSmaller
    [Finite V]
    {Source : Structure L V} {S AOnly BOnly : Set V}
    (P : MixedGeometricPiece Source S AOnly BOnly)
    (hMinimal : ∀ Q : MixedGeometricPiece Source S AOnly BOnly,
      P.nonrootCount ≤ Q.nonrootCount)
    (Q : MixedGeometricPiece Source S AOnly BOnly) :
    ¬ Q.nonrootCount < P.nonrootCount :=
  Nat.not_lt_of_ge (hMinimal Q)

/-- If P is a globally smallest genuine mixed source piece,
no OTHER genuine mixed geometric piece may have a selected
nonroot component properly contained in that of P.

This is the exact contradiction interface for the printed
Claim 2 "proper sub-piece" step. Its premises demand a
real geometric piece with all closure conditions, not merely
an arbitrary smaller vertex subset. -/
theorem minimalMixedGeometricPiece_no_proper_mixed_component
    [Finite V]
    {Source : Structure L V} {S AOnly BOnly : Set V}
    (P : MixedGeometricPiece Source S AOnly BOnly)
    (hMinimal : ∀ Q : MixedGeometricPiece Source S AOnly BOnly,
      P.nonrootCount ≤ Q.nonrootCount)
    (Q : MixedGeometricPiece Source S AOnly BOnly)
    (hProper :
      functionalComponentFrom Source
        (Set.range Q.data.roots) Q.data.left ⊂
      functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left) :
    False := by
  have hLess : Q.nonrootCount < P.nonrootCount := by
    dsimp [MixedGeometricPiece.nonrootCount]
    exact Set.ncard_lt_ncard hProper
  exact (minimalMixedGeometricPiece_no_strictSmaller
    P hMinimal Q) hLess

end AllThoseRamseyClasses.Lifts
