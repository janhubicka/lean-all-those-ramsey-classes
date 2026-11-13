import AllThoseRamseyClasses.Lifts.Claim2ActualOuterBRetainedCarrier

/-!
# Exact source-carrier image of B-active vertices after a selected-Q flip

A selected-Q replacement with exact outer carrier and no B-exclusive
Q vertices does more than provide retained representatives: the
B-active part of the NEW geometric source carrier is precisely the
image, under the NEW complete-complement embedding, of the B-active
retained complement vertices in the OLD outer carrier.

This is an equality of actual SOURCE sets, not of target-image sets.
It does not require injectivity of the weak target maps.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every B-active new outer SOURCE vertex comes from precisely
the retained B-active complement SOURCE vertices. This exact set
equation is the source-side counting interface for a same-Q
rank-decreasing successor. -/
theorem fullNativeSelectedOuter_Bactive_carrier_eq_retained_image
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
    {w : W | w ∈ NewPart ∧ flip w ∈ BActive} =
      iNewE '' {e : QE | iOldE e ∈ OldPart ∧
        f (iOldE e) ∈ BActive} := by
  ext w
  constructor
  · intro hw
    obtain ⟨e, he, _⟩ :=
      fullNativeSelectedOuter_Bactive_unique_retained_source
        iOldE iNewE iNewQ OldPart NewPart f flip BActive
        hCarrier hNoBFromQ hEAgree w hw.1 hw.2
    exact ⟨e, ⟨he.2.1, he.2.2⟩, he.1⟩
  · rintro ⟨e, he, rfl⟩
    exact fullNativeSelectedOuter_retained_Bactive_survives
      iOldE iNewE iNewQ OldPart NewPart f flip BActive
      hCarrier hEAgree e he.1 he.2

end AllThoseRamseyClasses.Lifts
