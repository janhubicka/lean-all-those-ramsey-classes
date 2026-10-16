import AllThoseRamseyClasses.Lifts.WeakMinimalGeometricChart

/-!
# Positive root width for genuine pieces of connected forbidden sources

The global 2019 lift adds new relations only for POSITIVE root widths.
The minimal closed separator selected from an arbitrary finite source
may be empty if the source is disconnected. In a connected forbidden
source, any two selected vertices joined by a Gaifman path already
have an empty-cut path. A genuine minimal separator between them
therefore cannot be empty, so its Fin n root tuple has n > 0.

We state the weakest useful hypothesis, namely the actual connecting
path between the two chosen vertices, rather than inventing a new
notion of global connectedness.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A minimal closed separator between vertices which are connected
in the entire source Gaifman graph cannot be the empty set. -/
theorem minimalClosedSeparator_nonempty_of_emptyCut_path
    (A : Structure L V)
    (R : Set V)
    (x y : {z : V // z ∉ R})
    (hmin : IsMinimalClosedSeparator A R x y)
    (hConnected : ReachOutside A.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : V // z ∉ ∅})) :
    R.Nonempty := by
  by_contra hnot
  have hR : R = ∅ := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro z hz
    exact hnot ⟨z, hz⟩
  cases hR
  exact hmin.2.1 (by simpa using hConnected)

/-- An ACTUAL native geometric piece cut out between vertices
connected in the full source has positive width. -/
theorem geometricPiece_positiveWidth_of_emptyCut_path
    (A : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData A n)
    (hConnected : ReachOutside A.graph (∅ : Set V)
      (⟨d.left.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨d.right.1, by simp⟩ : {z : V // z ∉ ∅})) :
    0 < n := by
  have hCut : (Set.range d.roots).Nonempty :=
    minimalClosedSeparator_nonempty_of_emptyCut_path
      A (Set.range d.roots) d.left d.right d.minimal hConnected
  apply Nat.pos_of_ne_zero
  intro hz
  subst n
  obtain ⟨_z, i, _hi⟩ := hCut
  exact Fin.elim0 i

variable {H E F W U : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L W} {Source : Structure L U}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- The weak free-amalgam geometric selection yields a TRUE
positive-width forbidden piece when the two source witnesses are
connected before deleting the common-root preimage.

This is the missing positivity premise for the global
quotient-indexed canonical piece symbol, NOT a root-image
injectivity assertion. -/
theorem weakFreePartition_hasPositiveForbiddenGeometricPiece
    [Finite U]
    (Forbidden : ∀ {T : Type v}, Structure L T → Prop)
    (hForbidden : Forbidden Source)
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) (hf : Source.IsWeakHomomorphism Whole f)
    (x y : U)
    (hx : x ∈ weakFreeLeftPart (sL := sL) (iL := iL) f)
    (hy : y ∈ weakFreeRightPart
      (sL := sL) (iL := iL) (iR := iR) f)
    (hConnected : ReachOutside Source.graph (∅ : Set U)
      (⟨x, by simp⟩ : {z : U // z ∉ ∅})
      (⟨y, by simp⟩ : {z : U // z ∉ ∅})) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData Source n),
      0 < n ∧
      Set.range d.roots ⊆
        weakFreeRootPart (sL := sL) (iL := iL) f ∧
      d.left.1 = x ∧ d.right.1 = y ∧
      geometricFunctionalRootedPattern Source d ∈
        forbiddenGeometricFunctionalPieces Forbidden n := by
  obtain ⟨n, d, hRoot, hLeft, hRight, hPiece⟩ :=
    weakFreePartition_hasForbiddenGeometricPiece
      Forbidden hForbidden hfree f hf x y hx hy
  have hPathD : ReachOutside Source.graph (∅ : Set U)
      (⟨d.left.1, by simp⟩ : {z : U // z ∉ ∅})
      (⟨d.right.1, by simp⟩ : {z : U // z ∉ ∅}) := by
    simpa only [hLeft, hRight] using hConnected
  exact ⟨n, d,
    geometricPiece_positiveWidth_of_emptyCut_path Source d hPathD,
    hRoot, hLeft, hRight, hPiece⟩

end AllThoseRamseyClasses.Lifts
