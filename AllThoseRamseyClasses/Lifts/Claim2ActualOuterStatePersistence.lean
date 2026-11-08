import AllThoseRamseyClasses.Lifts.Claim2ClosedContextNoEscape
import AllThoseRamseyClasses.Lifts.GlobalFlipClosedOuterContext

/-!
# Two exact geometric eligibility invariants after a same-Q inner flip

The concrete right-to-left source successor now produces an ACTUAL
new outer minimal-closed-separator geometric piece, with exactly
the old ordered root's target coordinates, and its entire carrier
is the transported Q+unchanged-complement context.

Two essential Track C eligibility conditions for the NEXT step
are automatic from these established source certificates:

(1) If the OLD full outer ordered root maps to the common target
    seam, the NEW root does too, because its target coordinates
    are literally identical. The new genuine geometric outer
    piece is therefore automatically no-escape relative to that
    same full seam (the verified geometric-piece lemma).
    No new closed-context/no-escape assumption is required.

(2) If an A-exclusive source vertex lay in the old outer piece
    and every vertex of the flipped inner selected component
    was NOT A-exclusive, that anchor survived in the UNCHANGED
    native functional complement. The exact full source carrier
    equation puts its image in the NEW geometric outer piece,
    and complement target-map agreement preserves its A-only
    status exactly.

Both are statements about actual source vertices and exact
full native embeddings. Neither turns a weak EHN target map
into an injection or takes a forbidden image quotient.

These invariants do not show that a B-only flippable subpiece
exists at every positive rank, or that the singleton-boundary
condition persists in arbitrary mixed-root states.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The old/new actual geometric outer roots have IDENTICAL
target coordinates. Hence old seam containment transfers to
the new root, and the new source geometric outer carrier is
automatically no-escape for that seam. This needs neither
source-map injectivity nor a comparison of root cuts. -/
theorem geometricOuterRootSeam_noEscape_of_targetCoordinates
    {V W UX UA UT : Type}
    (Old : Structure L V) (New : Structure L W)
    {n : ℕ}
    (outer : GeometricFunctionalPieceData Old n)
    (newOuter : GeometricFunctionalPieceData New n)
    (Target : Structure L UT)
    (X : Structure L UX) (Left : Structure L UA)
    (iLeft : Structure.Embedding X Left)
    (jLeft : Structure.Embedding Left Target)
    (f : V → UT) (flip : W → UT)
    (hTargetCoords : ∀ i : Fin n,
      flip (newOuter.roots i) = f (outer.roots i))
    (hOldSeam : Set.range outer.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f) :
    (Set.range newOuter.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) flip) ∧
    FunctionalContextNoEscapeOutsideSeam New
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip)
      (geometricPieceVertices New newOuter) := by
  have hNewSeam : Set.range newOuter.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) flip := by
    rintro w ⟨i, rfl⟩
    obtain ⟨r, hr⟩ := hOldSeam ⟨i, rfl⟩
    exact ⟨r, hr.trans (hTargetCoords i).symm⟩
  exact ⟨hNewSeam,
    geometricPiece_noEscapeOutsideContainingSeam
      New newOuter
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) flip)
      hNewSeam⟩

/-- An A-exclusive SOURCE anchor in the old entire outer geometric
piece survives the SAME genuine replacement of an A-free inner
selected component. It remains a SOURCE vertex of the ACTUAL new
geometric outer piece, with EXACTLY the old target image.

This conclusion is conditional only on the full native
complement-coordinate agreement, absence of A-exclusive vertices
in the removed chosen inner component, and the exact geometric
carrier equation already derived for truly selected nested Q.
No source collision is identified away under a weak target map. -/
theorem geometricOuterAnchor_survives_selectedInnerFlip
    {V W UT : Type}
    (Old : Structure L V)
    {n m : ℕ}
    (outer : GeometricFunctionalPieceData Old n)
    (inner : GeometricFunctionalPieceData Old m)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (newOuter : GeometricFunctionalPieceData New n)
    (hCarrier :
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old outer inner)) =
          geometricPieceVertices New newOuter)
    (f : V → UT) (flip : W → UT)
    (hSameComplement :
      ∀ b : (geometricGlobalComplementChart Old inner).Carrier,
        flip (iE b) = f b.1)
    (AOnly : Set UT)
    (a : V)
    (haOuter : a ∈ geometricPieceVertices Old outer)
    (haA : f a ∈ AOnly)
    (hInnerNoA : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left →
        f z ∉ AOnly) :
    ∃ anew : W,
      anew ∈ geometricPieceVertices New newOuter ∧
      flip anew = f a ∧
      flip anew ∈ AOnly := by
  have haPrivate : a ∉
      functionalComponentFrom Old
        (Set.range inner.roots) inner.left := by
    intro haD
    exact hInnerNoA a haD haA
  let b : (geometricGlobalComplementChart Old inner).Carrier :=
    ⟨a, haPrivate⟩
  have hbContext :
      b ∈ oldOuterContextInInnerComplement Old outer inner :=
    haOuter
  have hbNew :
      iE b ∈ geometricPieceVertices New newOuter := by
    rw [← hCarrier]
    exact Or.inr ⟨b, hbContext, rfl⟩
  have hbSame : flip (iE b) = f a :=
    hSameComplement b
  exact ⟨iE b, hbNew, hbSame, hbSame.symm ▸ haA⟩

end AllThoseRamseyClasses.Lifts
