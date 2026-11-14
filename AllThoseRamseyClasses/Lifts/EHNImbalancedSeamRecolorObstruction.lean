import AllThoseRamseyClasses.Lifts.EHNSeamFibreExactCount
import AllThoseRamseyClasses.Lifts.EHNLocalSeamRecolorFailure

/-!
# Track D: native minimal forbidden EHN witness, occupied seam destination

The previously verified #1163 fresh-seam obstruction requires a
target seam point UNUSED by the entire original source witness.
Here the global unused-point hypothesis is replaced by a precise
source fibre imbalance: the old f(a)-fibre has at least TWO more
original vertices than the target t-fibre.

Even if t is occupied, this makes a one-vertex seam recolouring
STRICTLY decrease the total ordered original-source seam collision
count. A lexicographically minimal genuine forbidden EHN witness
therefore cannot retain EHN under such a recolouring.

This is a CONDITIONAL obstruction: it neither constructs an EHN
recolouring nor proves unrestricted root injectivity, Claim 1/2,
strong amalgamation or any Ramsey theorem. The old language FULL
test/relation/function locality trichotomy still applies.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- New ACTUAL original-source theorem, valid even when the
destination target seam point is occupied by other source vertices.

For a lexicographically minimal genuine forbidden EHN witness,
a one-vertex seam move from f(a) to t with a sufficiently SMALL
destination fibre cannot itself be a new original EHN map of the
SAME forbidden native source. Both primary source support and
secondary total ordered source seam collisions are accounted for.

The finite Fintype/DecidableEq instances add no mathematical
hypothesis: the witness already carries a finite source carrier. -/
theorem lexMinimalForbiddenWitness_imbalancedSeamRecolor_notEHN
    {F : ∀ {W : Type}, Structure L W → Prop}
    {UT : Type} {Target : Structure L UT}
    (LeftExclusive Seam : Set UT)
    (hDisjoint : Disjoint LeftExclusive Seam)
    (w : ForbiddenEHNWitness F Target)
    [Fintype w.Carrier] [DecidableEq w.Carrier]
    (hPrimary : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount LeftExclusive ≤
        v.sourceSupportCount LeftExclusive)
    (hSecondary : ∀ v : ForbiddenEHNWitness F Target,
      v.sourceSupportCount LeftExclusive =
        w.sourceSupportCount LeftExclusive →
      w.seamCollisionPairCount Seam ≤
        v.seamCollisionPairCount Seam)
    (a : w.Carrier) (t : UT)
    (hDifferent : w.toTarget a ≠ t)
    (hSourceSeam : w.toTarget a ∈ Seam)
    (hTargetSeam : t ∈ Seam)
    (hImbalance :
      (originalSourceFibreExcept w.toTarget a t).card <
        (originalSourceFibreExcept
          w.toTarget a (w.toTarget a)).card) :
    ¬ w.source.IsEHNHomomorphismEmbedding Target
      (originalSourceSeamOneVertexRecolor w.toTarget a t) := by
  classical
  letI : Finite w.Carrier := w.finiteCarrier
  intro hNewEHN
  let g : w.Carrier → UT :=
    originalSourceSeamOneVertexRecolor w.toTarget a t
  have hCountDrop :
      (originalSourceSeamCollisionPairs g Seam).card <
        (originalSourceSeamCollisionPairs w.toTarget Seam).card :=
    (originalSourceSeam_oneVertexRecolor_strictDrop_iff
      w.toTarget Seam a t
      hDifferent hSourceSeam hTargetSeam).2 hImbalance
  have hNativeCountDrop :
      Nat.card {p : w.Carrier × w.Carrier //
        p.1 ≠ p.2 ∧ g p.1 = g p.2 ∧ g p.1 ∈ Seam} <
      w.seamCollisionPairCount Seam := by
    change
      Nat.card {p : w.Carrier × w.Carrier //
        p.1 ≠ p.2 ∧ g p.1 = g p.2 ∧ g p.1 ∈ Seam} <
      Nat.card {p : w.Carrier × w.Carrier //
        p.1 ≠ p.2 ∧
          w.toTarget p.1 = w.toTarget p.2 ∧
          w.toTarget p.1 ∈ Seam}
    rw [← originalSourceSeamCollisionPairs_card_eq_nat_card g Seam,
      ← originalSourceSeamCollisionPairs_card_eq_nat_card w.toTarget Seam]
    exact hCountDrop
  have hStay : ∀ x : w.Carrier,
      w.toTarget x ∈ Seam → g x ∈ Seam := by
    intro x hx
    by_cases hxa : x = a
    · subst x
      simpa [g, originalSourceSeamOneVertexRecolor] using hTargetSeam
    · simpa [g, originalSourceSeamOneVertexRecolor, hxa] using hx
  have hFixed : ∀ x : w.Carrier,
      w.toTarget x ∉ Seam → g x = w.toTarget x := by
    intro x hx
    have hxa : x ≠ a := by
      intro h
      subst x
      exact hx hSourceSeam
    simp [g, originalSourceSeamOneVertexRecolor, hxa]
  exact lexMinimalForbiddenWitness_no_seamOnlyCollisionReducingEHNRecoloring
    LeftExclusive Seam hDisjoint w hPrimary hSecondary
    g hNewEHN hStay hFixed hNativeCountDrop

end AllThoseRamseyClasses.Lifts
