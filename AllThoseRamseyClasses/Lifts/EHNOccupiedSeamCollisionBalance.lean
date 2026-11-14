import AllThoseRamseyClasses.Lifts.EHNLexMinimalSeamCollisionWitness
import Mathlib.Tactic

/-!
# Track D: exact finite ordered seam-collision balance for an occupied destination

Recolour ONE original source vertex a from c=f(a) to a target seam point d,
which need not be unused. Let s=V\{a}. The only changed ordered
distinct-source collision pairs have a as one endpoint:
- old lost pairs: (a,x),(x,a) for x in s with f(x)=c;
- new gained pairs: (a,x),(x,a) for x in s with f(x)=d.

All pairs with both coordinates in s are unchanged. Therefore
  NewCount + 2 * |s ∩ f^{-1}(c)|
    = OldCount + 2 * |s ∩ f^{-1}(d)|.

The two multiplicities count actual ORIGINAL SOURCE vertices, never
image vertices. This equality holds even for occupied d, or d=c.
With d≠c, the destination count includes all its original source
preimages, and strict descent is precisely the imbalance condition
|f^{-1}(d)| < |f^{-1}(c)| - 1.

THIS MODULE is a numerical statement about the SAME original source.
It does not infer EHN preservation or transfer forbidden status through
a source-image quotient. The native old relation, function and full
irreducible-test obligations remain open in the unrestricted Claim 2.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

/-- Indicator for a true ordered pair of distinct original source
vertices collapsed to the same actual target seam point. -/
noncomputable def orderedSeamCollisionIndicator
    {V UT : Type} (f : V → UT) (Seam : Set UT)
    (x y : V) : ℕ := by
  classical
  exact if x ≠ y ∧ f x = f y ∧ f x ∈ Seam then 1 else 0

/-- Count ACTUAL original ordered source pairs collapsed at the
common seam, without assuming global injectivity of the target map. -/
noncomputable def orderedSeamCollisionCount
    {V UT : Type} [Fintype V]
    (f : V → UT) (Seam : Set UT) : ℕ :=
  ∑ x : V, ∑ y : V, orderedSeamCollisionIndicator f Seam x y

/-- A finite ordered double sum decomposes into the pairs avoiding
a on both sides, the row/column touching a, and the diagonal. -/
private theorem finiteOrderedPairSum_splitAt
    {V : Type} [Fintype V] [DecidableEq V]
    (a : V) (q : V → V → ℕ) :
    (∑ x : V, ∑ y : V, q x y) =
      (((∑ x ∈ Finset.univ.erase a,
            ∑ y ∈ Finset.univ.erase a, q x y) +
        (∑ x ∈ Finset.univ.erase a, q x a)) +
        (∑ y ∈ Finset.univ.erase a, q a y)) +
        q a a := by
  classical
  let s : Finset V := Finset.univ.erase a
  have hErase (h : V → ℕ) :
      (∑ x : V, h x) = (∑ x ∈ s, h x) + h a := by
    simpa only [s] using
      (Finset.sum_erase_add (Finset.univ) h
        (Finset.mem_univ a)).symm
  calc
    (∑ x : V, ∑ y : V, q x y) =
        (∑ x ∈ s, ∑ y : V, q x y) +
          (∑ y : V, q a y) := hErase _
    _ = (∑ x ∈ s, ((∑ y ∈ s, q x y) + q x a)) +
          ((∑ y ∈ s, q a y) + q a a) := by
      simp_rw [hErase]
    _ = (((∑ x ∈ s, ∑ y ∈ s, q x y) +
          (∑ x ∈ s, q x a)) +
          (∑ y ∈ s, q a y)) + q a a := by
      rw [Finset.sum_add_distrib]
      omega

/-- Indicators on a fixed finite set count exactly the selected
source vertices. -/
private theorem finiteIndicatorSum_eq_filterCard
    {V : Type} (s : Finset V) (P : V → Prop) [DecidablePred P] :
    (∑ x ∈ s, if P x then (1 : ℕ) else 0) =
      (s.filter P).card := by
  classical
  simp [Finset.sum_ite]

/-- The precise occupied-target numerical identity for a single
vertex recolouring on ANY FINITE actual original source.

Both c=f(a) and d must lie in the target seam; d need not
be globally fresh, and the result also allows d=c.
All counts are ORDERED distinct-source seam-collision pairs.

For d ≠ c, the right-hand destination fibre count is the FULL
old d-fibre; the old c-fibre count omits exactly a itself. -/
theorem finiteOneVertexOccupiedSeamRecolor_orderedCollisionBalance
    {V UT : Type} [Fintype V] [DecidableEq V]
    (f : V → UT) (Seam : Set UT)
    (a : V) (d : UT)
    (hOldSeam : f a ∈ Seam) (hDestSeam : d ∈ Seam) :
    let g : V → UT := fun z => if z = a then d else f z
    orderedSeamCollisionCount g Seam +
      2 * ((Finset.univ.erase a).filter
        (fun x : V => f x = f a)).card =
    orderedSeamCollisionCount f Seam +
      2 * ((Finset.univ.erase a).filter
        (fun x : V => f x = d)).card := by
  classical
  let s : Finset V := Finset.univ.erase a
  let g : V → UT := fun z => if z = a then d else f z
  let q : (V → UT) → V → V → ℕ :=
    fun h x y => orderedSeamCollisionIndicator h Seam x y
  let U : (V → UT) → ℕ :=
    fun h => ∑ x ∈ s, ∑ y ∈ s, q h x y
  let M : ℕ := (s.filter (fun x : V => f x = f a)).card
  let K : ℕ := (s.filter (fun x : V => f x = d)).card

  have hSource (x : V) (hx : x ∈ s) : x ≠ a :=
    (Finset.mem_erase.mp hx).1
  have hSameCommon : U g = U f := by
    dsimp [U]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    have hx' := hSource x hx
    have hy' := hSource y hy
    simp [q, orderedSeamCollisionIndicator, g, hx', hy']

  have hOldRow (x : V) (hx : x ∈ s) :
      q f x a = if f x = f a then 1 else 0 := by
    have hxa := hSource x hx
    by_cases hEq : f x = f a
    · simp [q, orderedSeamCollisionIndicator, hxa, hEq, hOldSeam]
    · simp [q, orderedSeamCollisionIndicator, hxa, hEq]
  have hOldCol (x : V) (hx : x ∈ s) :
      q f a x = if f x = f a then 1 else 0 := by
    have hxa := hSource x hx
    by_cases hEq : f x = f a
    · simp [q, orderedSeamCollisionIndicator, hxa.symm, hEq, hOldSeam]
    · have hNe : f a ≠ f x := Ne.symm hEq
      simp [q, orderedSeamCollisionIndicator, hxa.symm, hEq, hNe]
  have hNewRow (x : V) (hx : x ∈ s) :
      q g x a = if f x = d then 1 else 0 := by
    have hxa := hSource x hx
    by_cases hEq : f x = d
    · simp [q, orderedSeamCollisionIndicator, g, hxa, hEq, hDestSeam]
    · simp [q, orderedSeamCollisionIndicator, g, hxa, hEq]
  have hNewCol (x : V) (hx : x ∈ s) :
      q g a x = if f x = d then 1 else 0 := by
    have hxa := hSource x hx
    by_cases hEq : f x = d
    · simp [q, orderedSeamCollisionIndicator, g, hxa.symm, hEq, hDestSeam]
    · have hNe : d ≠ f x := Ne.symm hEq
      simp [q, orderedSeamCollisionIndicator, g, hxa.symm, hEq, hNe]

  have hOldRowSum :
      (∑ x ∈ s, q f x a) = M := by
    calc
      _ = ∑ x ∈ s, if f x = f a then 1 else 0 :=
        Finset.sum_congr rfl hOldRow
      _ = M := finiteIndicatorSum_eq_filterCard s _
  have hOldColSum :
      (∑ x ∈ s, q f a x) = M := by
    calc
      _ = ∑ x ∈ s, if f x = f a then 1 else 0 :=
        Finset.sum_congr rfl hOldCol
      _ = M := finiteIndicatorSum_eq_filterCard s _
  have hNewRowSum :
      (∑ x ∈ s, q g x a) = K := by
    calc
      _ = ∑ x ∈ s, if f x = d then 1 else 0 :=
        Finset.sum_congr rfl hNewRow
      _ = K := finiteIndicatorSum_eq_filterCard s _
  have hNewColSum :
      (∑ x ∈ s, q g a x) = K := by
    calc
      _ = ∑ x ∈ s, if f x = d then 1 else 0 :=
        Finset.sum_congr rfl hNewCol
      _ = K := finiteIndicatorSum_eq_filterCard s _

  have hDiagonalF : q f a a = 0 := by
    simp [q, orderedSeamCollisionIndicator]
  have hDiagonalG : q g a a = 0 := by
    simp [q, orderedSeamCollisionIndicator]
  have hOld :
      orderedSeamCollisionCount f Seam = U f + M + M := by
    calc
      orderedSeamCollisionCount f Seam =
          (((U f + (∑ x ∈ s, q f x a)) +
            (∑ y ∈ s, q f a y)) + q f a a) := by
          exact finiteOrderedPairSum_splitAt a (q f)
      _ = U f + M + M := by
        rw [hOldRowSum, hOldColSum, hDiagonalF]
        omega
  have hNew :
      orderedSeamCollisionCount g Seam = U g + K + K := by
    calc
      orderedSeamCollisionCount g Seam =
          (((U g + (∑ x ∈ s, q g x a)) +
            (∑ y ∈ s, q g a y)) + q g a a) := by
          exact finiteOrderedPairSum_splitAt a (q g)
      _ = U g + K + K := by
        rw [hNewRowSum, hNewColSum, hDiagonalG]
        omega
  change orderedSeamCollisionCount g Seam + 2 * M =
    orderedSeamCollisionCount f Seam + 2 * K
  rw [hOld, hNew, hSameCommon]
  omega

end AllThoseRamseyClasses.Lifts
