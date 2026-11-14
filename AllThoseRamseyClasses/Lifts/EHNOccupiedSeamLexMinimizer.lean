import AllThoseRamseyClasses.Lifts.EHNOccupiedSeamCollisionBalance
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Track D: connect finite occupied-fibre counts to ORIGINAL forbidden EHN minimization

The finite double-sum count of ordered source collisions is not
a substitute for the source-pair Nat.card measure used by the
verified lexicographic minimizer. We prove their exact equality
on every genuine finite source, then derive a conditional
source-support-first/collision-second minimality contradiction
when an ACTUAL occupied-fibre recolouring preserves EHN.

The old and new maps have the SAME original finite source;
the recolouring does not require a target point outside the
old range. A strictly smaller occupied seam fibre is numerically
sufficient for strict collision descent; EHN preservation itself
remains a separate unsolved construction obligation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The finite double-sum count equals the EXACT source-pair
subtype Nat.card used by ForbiddenEHNWitness.seamCollisionPairCount.
No quotient or image-injection assumption is made. -/
theorem orderedSeamCollisionCount_eq_originalPairNatCard
    {V UT : Type} [Fintype V]
    (f : V → UT) (Seam : Set UT) :
    orderedSeamCollisionCount f Seam =
      Nat.card {p : V × V //
        p.1 ≠ p.2 ∧ f p.1 = f p.2 ∧ f p.1 ∈ Seam} := by
  classical
  let P : V × V → Prop :=
    fun p => p.1 ≠ p.2 ∧ f p.1 = f p.2 ∧ f p.1 ∈ Seam
  have hSubtype :
      Nat.card {p : V × V // P p} =
      ((Finset.univ : Finset (V × V)).filter P).card := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_subtype P)
  have hDouble :
      orderedSeamCollisionCount f Seam =
        ∑ p : V × V,
          orderedSeamCollisionIndicator f Seam p.1 p.2 := by
    unfold orderedSeamCollisionCount
    calc
      (∑ x : V, ∑ y : V,
        orderedSeamCollisionIndicator f Seam x y) =
          ∑ p ∈ (Finset.univ : Finset V).product Finset.univ,
            orderedSeamCollisionIndicator f Seam p.1 p.2 := by
          symm
          exact Finset.sum_product
            (Finset.univ : Finset V)
            (Finset.univ : Finset V)
            (fun p : V × V =>
              orderedSeamCollisionIndicator f Seam p.1 p.2)
      _ = ∑ p : V × V,
            orderedSeamCollisionIndicator f Seam p.1 p.2 := by
          simp
  have hFilter :
      (∑ p : V × V,
        orderedSeamCollisionIndicator f Seam p.1 p.2) =
      ((Finset.univ : Finset (V × V)).filter P).card := by
    simp [orderedSeamCollisionIndicator, P, Finset.sum_ite]
  change orderedSeamCollisionCount f Seam =
      Nat.card {p : V × V // P p}
  exact hDouble.trans (hFilter.trans hSubtype.symm)

/-- Genuine source-pair Nat.card formulation of the EXACT
occupied-seam row/column identity. This is now in the same
measure as the two-stage original forbidden EHN minimizer. -/
theorem finiteOneVertexOccupiedSeamRecolor_originalPairNatCardBalance
    {V UT : Type} [Fintype V] [DecidableEq V] [DecidableEq UT]
    (f : V → UT) (Seam : Set UT)
    (a : V) (d : UT)
    (hOldSeam : f a ∈ Seam) (hDestSeam : d ∈ Seam) :
    let g : V → UT := fun z => if z = a then d else f z
    Nat.card {p : V × V //
      p.1 ≠ p.2 ∧ g p.1 = g p.2 ∧ g p.1 ∈ Seam} +
      2 * ((Finset.univ.erase a).filter
        (fun x : V => f x = f a)).card =
    Nat.card {p : V × V //
      p.1 ≠ p.2 ∧ f p.1 = f p.2 ∧ f p.1 ∈ Seam} +
      2 * ((Finset.univ.erase a).filter
        (fun x : V => f x = d)).card := by
  classical
  have h := finiteOneVertexOccupiedSeamRecolor_orderedCollisionBalance
    f Seam a d hOldSeam hDestSeam
  simpa only [orderedSeamCollisionCount_eq_originalPairNatCard] using h

/-- A support-first, collision-second minimal ACTUAL forbidden EHN
witness cannot be recoloured at one source vertex to an occupied
common-seam target point with a strictly smaller number of OTHER
original source vertices in that target fibre, while preserving EHN.

The target value need not be globally unused. The strict numeric
decrease follows from the exact real-source-pair cardinal identity,
not an assumed collision-free destination. This is conditional
only on a genuine NEW native EHN map: the 2019 maximal common
canonical lift alone does NOT imply that hypothesis. -/
theorem lexMinimalForbiddenWitness_no_EHN_occupiedSeamDownshift
    {F : ∀ {W : Type}, Structure L W → Prop}
    {UT : Type} {Target : Structure L UT}
    (LeftExclusive Seam : Set UT)
    (hDisjoint : Disjoint LeftExclusive Seam)
    (w : ForbiddenEHNWitness F Target)
    (hPrimary : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount LeftExclusive ≤
        v.sourceSupportCount LeftExclusive)
    (hSecondary : ∀ v : ForbiddenEHNWitness F Target,
      v.sourceSupportCount LeftExclusive =
        w.sourceSupportCount LeftExclusive →
      w.seamCollisionPairCount Seam ≤
        v.seamCollisionPairCount Seam)
    [Fintype w.Carrier] [DecidableEq w.Carrier] [DecidableEq UT]
    (a : w.Carrier) (d : UT)
    (hOldSeam : w.toTarget a ∈ Seam)
    (hDestSeam : d ∈ Seam)
    (hLighter :
      ((Finset.univ.erase a).filter
        (fun x : w.Carrier => w.toTarget x = d)).card <
      ((Finset.univ.erase a).filter
        (fun x : w.Carrier => w.toTarget x = w.toTarget a)).card)
    (hNewEHN : w.source.IsEHNHomomorphismEmbedding Target
      (fun x : w.Carrier => if x = a then d else w.toTarget x)) :
    False := by
  classical
  let g : w.Carrier → UT :=
    fun x => if x = a then d else w.toTarget x
  have hStay : ∀ x : w.Carrier,
      w.toTarget x ∈ Seam → g x ∈ Seam := by
    intro x hx
    by_cases hxa : x = a
    · simp [g, hxa, hDestSeam]
    · simpa [g, hxa] using hx
  have hFixed : ∀ x : w.Carrier,
      w.toTarget x ∉ Seam → g x = w.toTarget x := by
    intro x hx
    have hxa : x ≠ a := by
      intro h
      apply hx
      simpa [h] using hOldSeam
    simp [g, hxa]
  have hBalance :=
    finiteOneVertexOccupiedSeamRecolor_originalPairNatCardBalance
      w.toTarget Seam a d hOldSeam hDestSeam
  have hDrop :
      Nat.card {p : w.Carrier × w.Carrier //
        p.1 ≠ p.2 ∧
        g p.1 = g p.2 ∧ g p.1 ∈ Seam} <
      w.seamCollisionPairCount Seam := by
    change Nat.card {p : w.Carrier × w.Carrier //
        p.1 ≠ p.2 ∧ g p.1 = g p.2 ∧ g p.1 ∈ Seam} <
      Nat.card {p : w.Carrier × w.Carrier //
        p.1 ≠ p.2 ∧
        w.toTarget p.1 = w.toTarget p.2 ∧
        w.toTarget p.1 ∈ Seam}
    dsimp only at hBalance
    omega
  exact lexMinimalForbiddenWitness_no_seamOnlyCollisionReducingEHNRecoloring
    LeftExclusive Seam hDisjoint
    w hPrimary hSecondary g hNewEHN hStay hFixed hDrop

end AllThoseRamseyClasses.Lifts
