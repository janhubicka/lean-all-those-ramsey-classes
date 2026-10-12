import AllThoseRamseyClasses.Published.WeakSizeTwoObligations2019

/-!
# Adversarial size obstruction to the small-WEAK-image A-boundary contract

The repaired exact W_j -> W_(j+1) conditional interface in
WeakSizeTwoObligations2019 is CORRECT but its weak-boundary geometry is
stronger than the native Hales--Jewett history currently supplies.

If a full embedding of a fixed closed A into the exact weak target
Old|TL exists and |TL| <= j, then necessarily |A| <= j.
Thus for j<|A|, no such certificate can exist for any maximal-rank
ordinary reducible test requiring this branch. In particular the
rank-one-to-two step CANNOT generally use a whole large A as the
boundary inside weak image sets of size <=1.

The earlier closed-rank-j hull construction allowed A to be larger
than j because closure can adjoin extra outputs without increasing
generating rank. This relaxation is precisely what W_j does NOT
supply. Merely replacing the R_j premise by W_j is not justified.

This negative cardinal observation is a constraint on the proposed
conditional approach, not a disproof of the repaired Theorem 2.18.
Alternative interfaces may use a smaller CLOSED Q in K when it exists
and fits the weak images, or retain controlled rank-j closed hulls.

No universal weak-j Picture increment is claimed.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Any induced embedding of the FULL A into a weak target vertex set
T of size at most j forces |A| <= j, regardless of closure rules. -/
theorem native2019_small_weak_A_boundary_card_le
    {VA VD : Type v}
    [Finite VA] [Finite VD]
    (D : RelStructure L VD)
    (A : RelStructure L VA)
    (T : Finset VD)
    (a : Embedding A (D.induce (↑T : Set VD)))
    (j : ℕ) (hT : T.card ≤ j) :
    Nat.card VA ≤ j := by
  classical
  letI : Fintype VA := Fintype.ofFinite VA
  letI : Fintype VD := Fintype.ofFinite VD
  letI : Fintype (↑T : Set VD) := Fintype.ofFinite (↑T : Set VD)
  have hEmb : Fintype.card VA ≤ Fintype.card (↑T : Set VD) :=
    Fintype.card_le_of_injective a a.injective
  have hSet : Fintype.card (↑T : Set VD) = T.card := by
    simp
  rw [Nat.card_eq_fintype_card]
  omega

/-- In particular, if a selected maximal weak reducible source genuinely
requires a geometry certificate for ONE fixed A, then |A| <= j.

For j<|A| the previous conditional certificate cannot be supplied
on that source. This is a negative test of the interface, not of the
original class theorem. -/
theorem native2019_selected_weak_A_geometry_forces_A_card_le
    {VC VD VA : Type v}
    [Finite VC] [Finite VD] [Finite VA]
    (rules : ClosureDescription L)
    (C : RelStructure L VC)
    (D : RelStructure L VD)
    (A : RelStructure L VA)
    (j : ℕ)
    (hGeometry :
      Has2019SelectedSmallWeakABoundaryGeometry rules C D A j)
    (S : Finset VC)
    (hS : S.card ≤ j+1)
    (hMax : USize rules (C.induce (↑S : Set VC)) = S.card)
    (hRed : ¬ (C.induce (↑S : Set VC)).Irreducible) :
    Nat.card VA ≤ j := by
  obtain ⟨d, TL, TR, pL, pR, q, aL, aR,
      hSizeL, _, _, _, _, _, _, _⟩ :=
    hGeometry S hS hMax hRed
  exact native2019_small_weak_A_boundary_card_le
    D A TL aL j hSizeL

end AllThoseRamseyClasses.Published
