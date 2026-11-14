import AllThoseRamseyClasses.Lifts.Claim2ActualOuterBActiveImage

/-!
# Source-cardinality bookkeeping for a genuine selected-Q replacement

For the original 2019 Claim 2 flip, the target map is only an EHN
homomorphism-embedding, and hence counts MUST refer to actual source
vertices rather than distinct target images.

When the inserted Q contributes no B-active images and the new outer
carrier is exactly Q together with the retained E vertices,
its B-active source count equals the B-active count of E in the OLD
outer carrier. The latter injects into the old outer B-active sources.

If an old outer B-active source vertex is absent from the old
complete-complement image, the count drops strictly. This final
hypothesis is explicit: no geometric consequence or existence of a
selected flippable piece is hidden in the bookkeeping theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The retained B-active complete-complement vertices inject into
the actual OLD outer B-active source vertices. This map uses the
FULL native complement embedding, not the weak target map. -/
private def retainedBIntoOld
    {V QE UT : Type}
    {Old : Structure L V}
    {Complement : Structure L QE}
    (iOldE : Structure.Embedding Complement Old)
    (OldPart : Set V) (f : V → UT) (BActive : Set UT) :
    {e : QE // iOldE e ∈ OldPart ∧ f (iOldE e) ∈ BActive} ↪
      {v : V // v ∈ OldPart ∧ f v ∈ BActive} where
  toFun e := ⟨iOldE e.1, e.2⟩
  inj' := by
    intro e e' h
    apply Subtype.ext
    exact iOldE.injective (congrArg Subtype.val h)

/-- Exact B-active SOURCE cardinality after the same selected-Q
replacement: only old-outer retained E vertices contribute.
No finite-type assumption is necessary for this equality, since
the complete-complement embedding is genuinely injective. -/
theorem fullNativeSelectedOuter_Bactive_card_eq_retained
    {V W QE Q UT : Type}
    {Old : Structure L V} {New : Structure L W}
    {Complement : Structure L QE} {Replacement : Structure L Q}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (iNewQ : Structure.Embedding Replacement New)
    (OldPart : Set V) (NewPart : Set W)
    (f : V → UT) (flip : W → UT)
    (BActive : Set UT)
    (hCarrier : NewPart =
      iNewQ '' (Set.univ : Set Q) ∪
        iNewE '' (iOldE ⁻¹' OldPart))
    (hNoBFromQ : ∀ q : Q, flip (iNewQ q) ∉ BActive)
    (hEAgree : ∀ e : QE, flip (iNewE e) = f (iOldE e)) :
    Nat.card {w : W // w ∈ NewPart ∧ flip w ∈ BActive} =
      Nat.card {e : QE // iOldE e ∈ OldPart ∧
        f (iOldE e) ∈ BActive} := by
  classical
  have hEq : {w : W | w ∈ NewPart ∧ flip w ∈ BActive} =
      iNewE '' {e : QE | iOldE e ∈ OldPart ∧
        f (iOldE e) ∈ BActive} :=
    fullNativeSelectedOuter_Bactive_carrier_eq_retained_image
      iOldE iNewE iNewQ OldPart NewPart f flip BActive
      hCarrier hNoBFromQ hEAgree
  change Nat.card (↑({w : W | w ∈ NewPart ∧
    flip w ∈ BActive} : Set W)) =
      Nat.card (↑({e : QE | iOldE e ∈ OldPart ∧
        f (iOldE e) ∈ BActive} : Set QE))
  rw [hEq]
  exact Nat.card_image_of_injective iNewE.injective _

/-- An actual native selected-Q replacement with no B-active
Q vertices never increases B-active SOURCE support inside the
transported outer carrier. The old source is finite. -/
theorem fullNativeSelectedOuter_Bactive_card_le_old
    {V W QE Q UT : Type}
    {Old : Structure L V} {New : Structure L W}
    {Complement : Structure L QE} {Replacement : Structure L Q}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (iNewQ : Structure.Embedding Replacement New)
    (OldPart : Set V) (NewPart : Set W)
    (f : V → UT) (flip : W → UT)
    (BActive : Set UT)
    (hFiniteOld : Finite V)
    (hCarrier : NewPart =
      iNewQ '' (Set.univ : Set Q) ∪
        iNewE '' (iOldE ⁻¹' OldPart))
    (hNoBFromQ : ∀ q : Q, flip (iNewQ q) ∉ BActive)
    (hEAgree : ∀ e : QE, flip (iNewE e) = f (iOldE e)) :
    Nat.card {w : W // w ∈ NewPart ∧ flip w ∈ BActive} ≤
      Nat.card {v : V // v ∈ OldPart ∧ f v ∈ BActive} := by
  letI : Finite V := hFiniteOld
  have hEq :=
    fullNativeSelectedOuter_Bactive_card_eq_retained
      iOldE iNewE iNewQ OldPart NewPart f flip BActive
      hCarrier hNoBFromQ hEAgree
  have hBound :
      Nat.card {e : QE // iOldE e ∈ OldPart ∧
        f (iOldE e) ∈ BActive} ≤
      Nat.card {v : V // v ∈ OldPart ∧ f v ∈ BActive} :=
    Nat.card_le_card_of_injective
      (retainedBIntoOld iOldE OldPart f BActive)
      (retainedBIntoOld iOldE OldPart f BActive).injective
  exact hEq.trans_le hBound

/-- If there is an old outer B-active SOURCE vertex deleted from
the complete complement, the actual selected-Q replacement
STRICTLY decreases the outer B-active SOURCE rank.

Both old source and complete complement are finite. This is a
literal source deletion certificate, not an assumption that the
weak target map is injective, and no distinct-image count. -/
theorem fullNativeSelectedOuter_Bactive_card_lt_old_of_missing_retained
    {V W QE Q UT : Type}
    {Old : Structure L V} {New : Structure L W}
    {Complement : Structure L QE} {Replacement : Structure L Q}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (iNewQ : Structure.Embedding Replacement New)
    (OldPart : Set V) (NewPart : Set W)
    (f : V → UT) (flip : W → UT)
    (BActive : Set UT)
    (hFiniteOld : Finite V)
    (hFiniteE : Finite QE)
    (hCarrier : NewPart =
      iNewQ '' (Set.univ : Set Q) ∪
        iNewE '' (iOldE ⁻¹' OldPart))
    (hNoBFromQ : ∀ q : Q, flip (iNewQ q) ∉ BActive)
    (hEAgree : ∀ e : QE, flip (iNewE e) = f (iOldE e))
    (hMissing : ∃ v : V,
      v ∈ OldPart ∧ f v ∈ BActive ∧ v ∉ Set.range iOldE) :
    Nat.card {w : W // w ∈ NewPart ∧ flip w ∈ BActive} <
      Nat.card {v : V // v ∈ OldPart ∧ f v ∈ BActive} := by
  classical
  letI : Finite V := hFiniteOld
  letI : Finite QE := hFiniteE
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype QE := Fintype.ofFinite QE
  let g := retainedBIntoOld iOldE OldPart f BActive
  have hNotSurj : ¬ Function.Surjective g := by
    intro hSurj
    obtain ⟨v, hvPart, hvB, hvMissing⟩ := hMissing
    obtain ⟨e, he⟩ := hSurj
      (⟨v, ⟨hvPart, hvB⟩⟩ :
        {v : V // v ∈ OldPart ∧ f v ∈ BActive})
    exact hvMissing ⟨e.1, congrArg Subtype.val he⟩
  have hLtFintype :
      Fintype.card {e : QE // iOldE e ∈ OldPart ∧
        f (iOldE e) ∈ BActive} <
      Fintype.card {v : V // v ∈ OldPart ∧ f v ∈ BActive} :=
    Fintype.card_lt_of_injective_not_surjective
      g g.injective hNotSurj
  have hLt :
      Nat.card {e : QE // iOldE e ∈ OldPart ∧
        f (iOldE e) ∈ BActive} <
      Nat.card {v : V // v ∈ OldPart ∧ f v ∈ BActive} := by
    simpa only [Nat.card_eq_fintype_card] using hLtFintype
  exact (fullNativeSelectedOuter_Bactive_card_eq_retained
    iOldE iNewE iNewQ OldPart NewPart f flip BActive
    hCarrier hNoBFromQ hEAgree).trans_lt hLt

end AllThoseRamseyClasses.Lifts
