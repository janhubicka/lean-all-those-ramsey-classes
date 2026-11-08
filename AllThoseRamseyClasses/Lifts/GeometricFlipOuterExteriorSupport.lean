import AllThoseRamseyClasses.Lifts.Claim2TerminalLeftSupportAccounting

/-!
# Exterior SOURCE support is unchanged by an exact geometric outer flip

Two actual native full functional source diagrams share their
COMPLETE unchanged complement E, although the selected inner
piece has been replaced. Assume the true new older geometric
piece is exactly the transported context

  NewOuterVertices = iQ[all Q] ∪ iNewE[E ∩ OldOuterVertices].

If the old geometric inner piece is contained in the old outer
piece, the original outer vertices are exactly the analogous old
context. A previously verified source-level full free-amalgam
bijection then identifies every SOURCE vertex outside the old
and new outer pieces with the SAME complementary E vertex.

Consequently, whenever the old/new weak maps agree on the
entire unchanged complement, for ANY subset B of the target,
the cardinalities of source vertices OUTSIDE the actual old/new
geometric outer pieces whose target images belong to B are
EXACTLY equal.

This is stronger than an equality of target-image sets, and does
not require injectivity of the weak map, any ordered old root
tuple, generated-boundary equality, or comparability of the
two closed cuts. The exact new geometric carrier identity is
an explicit premise, proved for genuinely selected nested
canonical flips by Track A's with-carrier result (#927).

The result is a necessary Track C exterior invariant, but
does not itself construct a flippable successor or a terminal
contradiction.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An actual full native inner replacement preserving the entire
complement and the EXACT outer geometric carrier preserves the
B-only source-vertex count OUTSIDE that geometric outer piece.

This holds for ANY target subset, including the A-exclusive
and B-exclusive parts of the original 2019 common-witness target.
No target-map injectivity, weak-image quotient or root-set
nestedness is presumed. -/
theorem geometricFlip_actualOuterExterior_sourceSupport_card_eq
    {V W UT : Type} [Finite V] [Finite W]
    (Old : Structure L V)
    {n m : ℕ}
    (outer : GeometricFunctionalPieceData Old n)
    (inner : GeometricFunctionalPieceData Old m)
    (hInnerRoot : ∀ i : Fin m,
      inner.roots i ∈ geometricPieceVertices Old outer)
    (hInnerComponent :
      functionalComponentFrom Old
        (Set.range inner.roots) inner.left ⊆
          geometricPieceVertices Old outer)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (newOuter : GeometricFunctionalPieceData New n)
    (hExactCarrier :
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old outer inner)) =
          geometricPieceVertices New newOuter)
    (f : V → UT) (flip : W → UT)
    (hSameE : ∀ b : (geometricGlobalComplementChart Old inner).Carrier,
      flip (iE b) = f b.1)
    (TargetSet : Set UT) :
    Nat.card {w : W //
      w ∉ geometricPieceVertices New newOuter ∧
      flip w ∈ TargetSet} =
    Nat.card {v : V //
      v ∉ geometricPieceVertices Old outer ∧
      f v ∈ TargetSet} := by
  have hInnerInside :
      geometricPieceVertices Old inner ⊆
        geometricPieceVertices Old outer := by
    intro v hv
    rcases hv with hRoot | hComponent
    · obtain ⟨i, hi⟩ := hRoot
      exact hi ▸ hInnerRoot i
    · exact hInnerComponent hComponent
  have hOutside :=
    geometricInnerSubpiece_outsideSupport_card_eq
      Old outer inner hInnerInside Q New iQ iE hNewFree
      f flip TargetSet hSameE
  rw [hExactCarrier] at hOutside
  exact hOutside

end AllThoseRamseyClasses.Lifts
