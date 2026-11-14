import AllThoseRamseyClasses.Lifts.ForbiddenWeakWitnessMinimization
import Mathlib.Data.Set.Card

/-!
# Track D: two-stage minimization of actual forbidden EHN witnesses

The original printed Section 3 proof minimizes the number of
ORIGINAL source vertices whose image lies exclusively in the
left target side of a genuine functional free amalgam.
This is the correct source-support measure even when the
original EHN forbidden-source map is NOT injective.

A proposed collision-tolerant repair should be judged against
another ACTUAL original source measure: the number of ORDERED
pairs of DISTINCT original source vertices whose target
images are EQUAL and belong to the designated common seam.

This module proves that whenever one genuine finite forbidden
EHN witness exists, a witness may be chosen to MINIMIZE
left-exclusive SOURCE support first, then this seam-collision
pair count among all primary minimizers.

For this lex-minimal witness, there is no competing actual
forbidden EHN source map whose left support is NO LARGER and
whose seam-collision count is STRICTLY SMALLER.

This is the exact well-founded logical contract for a future
collision-repair operation. It does NOT supply such an operation,
prove a root-image quotient is full, establish Claim 1/Claim 2,
or complete original 2019 strong AP.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Number of ORDERED distinct original-source vertex pairs
collapsed by a genuine forbidden EHN witness to one point in
a specified actual target seam. Counts SOURCE pairs rather
than image vertices, and does not assume the map is injective.

The structure field finiteCarrier guarantees the counted
source pair type is finite. -/
noncomputable def ForbiddenEHNWitness.seamCollisionPairCount
    {F : ∀ {W : Type}, Structure L W → Prop}
    {UT : Type} {Target : Structure L UT}
    (w : ForbiddenEHNWitness F Target)
    (Seam : Set UT) : ℕ := by
  letI : Finite w.Carrier := w.finiteCarrier
  exact Nat.card {p : w.Carrier × w.Carrier //
      p.1 ≠ p.2 ∧
      w.toTarget p.1 = w.toTarget p.2 ∧
      w.toTarget p.1 ∈ Seam}

/-- TWO-STAGE actual original forbidden weak EHN minimization:
choose the smallest original SOURCE left-exclusive support,
then, among all witnesses with that minimal support, choose
one with the least number of collapsed ORIGINAL source pairs
whose common target vertex lies in the exact target seam.

The primary source carrier and EHN target map may vary between
candidate forbidden witnesses. Neither the family nor any weak
image quotient is assumed closed under arbitrary identification.
-/
theorem exists_minimalForbiddenEHNWitness_support_then_seamCollisions
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UT : Type} (Target : Structure L UT)
    (LeftExclusive Seam : Set UT)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ w : ForbiddenEHNWitness F Target,
      (∀ v : ForbiddenEHNWitness F Target,
        w.sourceSupportCount LeftExclusive ≤
          v.sourceSupportCount LeftExclusive) ∧
      (∀ v : ForbiddenEHNWitness F Target,
        v.sourceSupportCount LeftExclusive =
          w.sourceSupportCount LeftExclusive →
        w.seamCollisionPairCount Seam ≤
          v.seamCollisionPairCount Seam) := by
  classical
  obtain ⟨w0, hMin0⟩ :=
    exists_minimalForbiddenEHNWitness_support
      F Target LeftExclusive hExists
  let sizes : Set ℕ :=
    {n | ∃ (w : ForbiddenEHNWitness F Target),
      (∀ v : ForbiddenEHNWitness F Target,
        w.sourceSupportCount LeftExclusive ≤
          v.sourceSupportCount LeftExclusive) ∧
      w.seamCollisionPairCount Seam = n}
  have hNonempty : sizes.Nonempty := by
    exact ⟨w0.seamCollisionPairCount Seam,
      w0, hMin0, rfl⟩
  have hMin : sInf sizes ∈ sizes :=
    Nat.sInf_mem hNonempty
  obtain ⟨w, hPrimary, hCollisionEq⟩ := hMin
  refine ⟨w, hPrimary, ?_⟩
  intro v hEqual
  have hPrimaryV : ∀ t : ForbiddenEHNWitness F Target,
      v.sourceSupportCount LeftExclusive ≤
        t.sourceSupportCount LeftExclusive := by
    intro t
    rw [hEqual]
    exact hPrimary t
  have hV : v.seamCollisionPairCount Seam ∈ sizes :=
    ⟨v, hPrimaryV, rfl⟩
  rw [hCollisionEq]
  exact Nat.sInf_le hV

/-- The actual lex-minimal forbidden witness excludes ANY competing
source map with no higher original left SOURCE support and strictly
fewer collapsed ordered original SOURCE seam pairs.

It does not exclude a hypothetical repair which decreases seam
collisions but INCREASES left source support, nor does it claim
the existence of any collision-repairing flip. -/
theorem minimalForbiddenEHNWitness_no_weakSupport_and_strictCollisionDrop
    {F : ∀ {W : Type}, Structure L W → Prop}
    {UT : Type} {Target : Structure L UT}
    (LeftExclusive Seam : Set UT)
    (w : ForbiddenEHNWitness F Target)
    (hPrimary : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount LeftExclusive ≤
        v.sourceSupportCount LeftExclusive)
    (hSecondary : ∀ v : ForbiddenEHNWitness F Target,
      v.sourceSupportCount LeftExclusive =
        w.sourceSupportCount LeftExclusive →
      w.seamCollisionPairCount Seam ≤
        v.seamCollisionPairCount Seam)
    (v : ForbiddenEHNWitness F Target)
    (hNoSupportIncrease :
      v.sourceSupportCount LeftExclusive ≤
        w.sourceSupportCount LeftExclusive)
    (hCollisionDrop :
      v.seamCollisionPairCount Seam <
        w.seamCollisionPairCount Seam) :
    False := by
  have hEqualSupport :
      v.sourceSupportCount LeftExclusive =
        w.sourceSupportCount LeftExclusive :=
    Nat.le_antisymm hNoSupportIncrease (hPrimary v)
  exact (Nat.not_lt_of_ge
    (hSecondary v hEqualSupport)) hCollisionDrop

/-- Changing only ORIGINAL source vertices which already map
into the genuine target seam, and keeping their new target values
inside that same seam, preserves membership of EVERY original
source vertex in a disjoint target LeftExclusive set.

This is the exact native set-level reason that seam-only
collision repairs can preserve the printed primary SOURCE
support count. No EHN assumption is needed for the set equality. -/
theorem seamOnlyRecoloring_preserves_originalSourceSupport
    {V UT : Type} [Finite V]
    (f g : V → UT)
    (LeftExclusive Seam : Set UT)
    (hDisjoint : Disjoint LeftExclusive Seam)
    (hSeamStay : ∀ x : V, f x ∈ Seam → g x ∈ Seam)
    (hOutsideFixed : ∀ x : V, f x ∉ Seam → g x = f x) :
    Nat.card {x : V // f x ∈ LeftExclusive} =
      Nat.card {x : V // g x ∈ LeftExclusive} := by
  have hPred :
      (fun x : V => f x ∈ LeftExclusive) =
        (fun x : V => g x ∈ LeftExclusive) := by
    funext x
    apply propext
    by_cases hInSeam : f x ∈ Seam
    · have hGSeam : g x ∈ Seam := hSeamStay x hInSeam
      constructor
      · intro hLeft
        exact False.elim
          ((Set.disjoint_left.mp hDisjoint) hLeft hInSeam)
      · intro hLeft
        exact False.elim
          ((Set.disjoint_left.mp hDisjoint) hLeft hGSeam)
    · rw [hOutsideFixed x hInSeam]
  rw [hPred]

/-- A secondary collision-minimal actual forbidden witness admits
NO alternate EHN map of the SAME original forbidden native source
which only recolours original seam vertices WITHIN the same seam,
keeps every original nonseam vertex coordinate unchanged, and
reduces the number of distinct original source pairs collapsed
inside the seam.

Such a change preserves PRIMARY SOURCE left-exclusive support
automatically by the preceding verified set equality, hence it
contradicts the lexicographic minimizer. This local criterion
makes an admissible seam-only "collision splitting" map a precise
future proof obligation rather than assuming one exists.

No new source quotient, rooted piece flip, or target old-relation
reflection follows from this negative minimality criterion. -/
theorem lexMinimalForbiddenWitness_no_seamOnlyCollisionReducingEHNRecoloring
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
    (g : w.Carrier → UT)
    (hg : w.source.IsEHNHomomorphismEmbedding Target g)
    (hSeamStay : ∀ x : w.Carrier,
      w.toTarget x ∈ Seam → g x ∈ Seam)
    (hOutsideFixed : ∀ x : w.Carrier,
      w.toTarget x ∉ Seam → g x = w.toTarget x)
    (hCollisionDrop :
      Nat.card {p : w.Carrier × w.Carrier //
        p.1 ≠ p.2 ∧
        g p.1 = g p.2 ∧
        g p.1 ∈ Seam} <
      w.seamCollisionPairCount Seam) :
    False := by
  classical
  letI : Finite w.Carrier := w.finiteCarrier
  let v : ForbiddenEHNWitness F Target := {
    Carrier := w.Carrier
    finiteCarrier := w.finiteCarrier
    source := w.source
    forbidden := w.forbidden
    toTarget := g
    homEmbedding := hg
  }
  have hNoSupportIncrease :
      v.sourceSupportCount LeftExclusive ≤
        w.sourceSupportCount LeftExclusive := by
    have hCount :=
      seamOnlyRecoloring_preserves_originalSourceSupport
        w.toTarget g LeftExclusive Seam
        hDisjoint hSeamStay hOutsideFixed
    change Nat.card {x : w.Carrier // g x ∈ LeftExclusive} ≤
      Nat.card {x : w.Carrier //
        w.toTarget x ∈ LeftExclusive}
    exact le_of_eq hCount.symm
  have hDrop :
      v.seamCollisionPairCount Seam <
        w.seamCollisionPairCount Seam := hCollisionDrop
  exact minimalForbiddenEHNWitness_no_weakSupport_and_strictCollisionDrop
    LeftExclusive Seam w hPrimary hSecondary
    v hNoSupportIncrease hDrop

end AllThoseRamseyClasses.Lifts
