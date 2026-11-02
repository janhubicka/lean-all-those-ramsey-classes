import AllThoseRamseyClasses.Lifts.Claim2TerminalActualOneSidedFlip
import AllThoseRamseyClasses.Lifts.GlobalRightToLeftStrictSupport

/-!
# Claim 2 terminal exit from zero local B-exclusive SOURCE support

The Rank of Track C is the finite number of B-exclusive SOURCE
vertices inside the exact genuine geometric outer piece.

Rank zero itself implies the selected component is B-free, under
the real native full target free-amalgam structure.  In particular
this is NOT an extra geometric terminal hypothesis.

The actual original-global canonical A-to-B flip of the whole
terminal piece (proved in the parent terminal-flip module)
then constructs a forbidden source with no A-only vertices in
its new selected piece and the same exterior A-only source count.
Consequently it contradicts the ORIGINAL A-support minimizer.

The last remaining Claim 2 iteration obligation is to prove that
the terminal state found by strict B-descent has rank zero,
namely: every positive-B-count valid outer state admits a
genuine next B-only inner flip preserving its geometry/profile
and exterior context. This is not assumed here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Zero B-exclusive SOURCE count in the genuine outer geometric
piece implies there are NO B-only source vertices in its
selected nonroot component. No target map injectivity, bounded
function arity, or modification of the original forbidden
family is required. -/
theorem geometricPiece_noRight_of_zeroLocalRightSupport
    {V UX UA UB UT : Type}
    [Finite V]
    (Source : Structure L V)
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam
      iLeft iRight jLeft jRight)
    (f : V → UT)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (hZero :
      Nat.card {v : V //
        v ∈ geometricPieceVertices Source d ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} = 0) :
    ∀ z : V,
      z ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left →
      z ∉ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f := by
  classical
  intro z hz hRight
  have hTargetAgreeR (x : UX) :
      jRight (iRight x) = jLeft (iLeft x) := by
    exact ((hTargetFree.overlap
      (iLeft x) (iRight x)).mpr ⟨x, rfl, rfl⟩).symm
  have hRightSwapped :
      z ∈ weakFreeLeftPart
        (sL := iRight) (iL := jRight) f := by
    refine ⟨hRight.1, ?_⟩
    intro hRoot
    obtain ⟨x, hx⟩ := hRoot
    apply hRight.2
    exact ⟨x, (hTargetAgreeR x).symm.trans hx⟩
  have hTargetB :
      f z ∈ fullFreeRightExclusiveTarget iRight jRight :=
    (weakFreeLeftPart_iff_targetExclusive
      iRight jRight f z).mp hRightSwapped
  have hPositive :
      0 < Nat.card {v : V //
        v ∈ geometricPieceVertices Source d ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
    letI : Fintype {v : V //
        v ∈ geometricPieceVertices Source d ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} :=
      Fintype.ofFinite _
    have hNonempty :
        Nonempty {v : V //
          v ∈ geometricPieceVertices Source d ∧
          f v ∈ fullFreeRightExclusiveTarget iRight jRight} :=
      ⟨⟨z, Or.inr hz, hTargetB⟩⟩
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_pos_iff.mpr hNonempty)
  exact (Nat.ne_of_gt hPositive) hZero

/-- A zero local B-rank terminal ACTUAL geometric outer piece
contradicts the ORIGINAL left-support minimizer once the
exterior A-support invariant is supplied.

Unlike the previous form this does not postulate an independent
`hNoRight`: it derives that exact one-sidedness from the
natural-number rank whose strict descent is already formalized
in Track C. The final A-to-B full native forbidden-source flip
is constructed by the parent theorem. -/
theorem claim2_originalMinimizer_contradicted_by_zeroTerminalBSupport
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    (hFiniteF : ∀ {Z : Type} (A : Structure L Z), F A → Finite Z)
    {UT : Type} (Target : Structure L UT)
    {UX UA UB : Type}
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam
      iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right
      iLeft iRight)
    (wOriginal : ForbiddenEHNWitness F Target)
    (hOriginalMin : ∀ t : ForbiddenEHNWitness F Target,
      wOriginal.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
      t.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft))
    (OriginalContext : Set wOriginal.Carrier)
    (hOrigPositiveA : ∃ v : wOriginal.Carrier,
      v ∈ OriginalContext ∧
      wOriginal.toTarget v ∈
        fullFreeLeftExclusiveTarget iLeft jLeft)
    {V : Type} (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    (f : V → UT)
    (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
    {n : ℕ} (d : GeometricFunctionalPieceData Forbidden n)
    (hn : 0 < n)
    (hRootInSeam : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hZeroRightCount :
      Nat.card {v : V //
        v ∈ geometricPieceVertices Forbidden d ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} = 0)
    (hRootInj : Function.Injective
      (fun i : Fin n => f (d.roots i)))
    (hExteriorOriginal : 
      Nat.card {v : V //
        v ∉ geometricPieceVertices Forbidden d ∧
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
      Nat.card {v : wOriginal.Carrier //
        v ∉ OriginalContext ∧
        wOriginal.toTarget v ∈
          fullFreeLeftExclusiveTarget iLeft jLeft}) : False := by
  have hNoRight :
      ∀ z : V,
        z ∈ functionalComponentFrom Forbidden
          (Set.range d.roots) d.left →
        z ∉ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f :=
    geometricPiece_noRight_of_zeroLocalRightSupport
      Forbidden Target Left Right jLeft jRight
      X iLeft iRight hTargetFree f d hZeroRightCount
  exact claim2_originalMinimizer_contradicted_by_terminal_BFreePiece
    F hFiniteF Target Left Right jLeft jRight
    X iLeft iRight hTargetFree hCommon
    wOriginal hOriginalMin OriginalContext hOrigPositiveA
    Forbidden hFinite hForbidden f hf d hn
    hRootInSeam hNoRight hRootInj hExteriorOriginal

end AllThoseRamseyClasses.Lifts
