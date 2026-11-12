import AllThoseRamseyClasses.Lifts.Claim2SeamCollisionNewSideLocalization

/-!
# Seam collisions require injectivity only on the retained OLD complement

The earlier native collision-localization theorem used old injectivity
on the ENTIRE old common-seam preimage. Its proof actually compares
only source vertices from the unchanged full functional complement E.
We isolate the precisely weaker hypothesis: old weak-map injectivity
on `range iOldE ∩ f ⁻¹' Seam`.

Consequently a new seam collision either lies outside E, and therefore
on the literal new Q side of the full native free amalgam, or else
would contradict that complement-local injectivity.

A further sufficient condition for preserving new seam injectivity is
that no replacement Q-nonroot vertex maps into the target seam. This
root-reflection hypothesis is NOT established for the original selected-Q
flip. No target quotient, image-count assumption, or 2019 text change.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The unchanged full source complement is still seam-injective
provided the old map was injective ONLY on old complement vertices
mapping into the seam. No hypothesis on the rest of the old source. -/
theorem fullNativeReplacement_retainedComplement_seamInjective_of_local
    {V W E UT : Type}
    {Old : Structure L V} {New : Structure L W}
    {Complement : Structure L E}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (f : V → UT) (g : W → UT)
    (Seam : Set UT)
    (hOldLocalInj : Set.InjOn f
      (Set.range iOldE ∩ (f ⁻¹' Seam)))
    (hSameComplement : ∀ e : E,
      g (iNewE e) = f (iOldE e))
    (e₁ e₂ : E)
    (hSeam₁ : g (iNewE e₁) ∈ Seam)
    (hSeam₂ : g (iNewE e₂) ∈ Seam)
    (hEqual : g (iNewE e₁) = g (iNewE e₂)) :
    e₁ = e₂ := by
  have hOldSeam₁ : f (iOldE e₁) ∈ Seam := by
    rw [← hSameComplement e₁]
    exact hSeam₁
  have hOldSeam₂ : f (iOldE e₂) ∈ Seam := by
    rw [← hSameComplement e₂]
    exact hSeam₂
  have hOldEq : f (iOldE e₁) = f (iOldE e₂) := by
    calc
      f (iOldE e₁) = g (iNewE e₁) := (hSameComplement e₁).symm
      _ = g (iNewE e₂) := hEqual
      _ = f (iOldE e₂) := hSameComplement e₂
  have hFirst : iOldE e₁ ∈
      Set.range iOldE ∩ (f ⁻¹' Seam) :=
    ⟨⟨e₁, rfl⟩, hOldSeam₁⟩
  have hSecond : iOldE e₂ ∈
      Set.range iOldE ∩ (f ⁻¹' Seam) :=
    ⟨⟨e₂, rfl⟩, hOldSeam₂⟩
  exact iOldE.injective (hOldLocalInj hFirst hSecond hOldEq)

/-- The sharp localization: with only old complement-local seam
injectivity, any genuine NEW seam collision has an actual Q-side
source vertex outside the entire unchanged complement. In particular,
a possibly colliding OLD source outside that complement is irrelevant. -/
theorem fullNativeReplacement_newSeamCollision_hits_QOutsideComplement_of_local
    {R E Q V W UT : Type}
    {Root : Structure L R}
    {Complement : Structure L E}
    {Replacement : Structure L Q}
    {Old : Structure L V} {New : Structure L W}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (iNewQ : Structure.Embedding Replacement New)
    (qRoot : Structure.Embedding Root Replacement)
    (eRoot : Structure.Embedding Root Complement)
    (hNewFree : Structure.IsFreeAmalgam qRoot eRoot iNewQ iNewE)
    (f : V → UT) (g : W → UT)
    (Seam : Set UT)
    (hOldLocalInj : Set.InjOn f
      (Set.range iOldE ∩ (f ⁻¹' Seam)))
    (hSameComplement : ∀ e : E,
      g (iNewE e) = f (iOldE e))
    (x y : W)
    (hxSeam : g x ∈ Seam)
    (hySeam : g y ∈ Seam)
    (hEqual : g x = g y)
    (hDistinct : x ≠ y) :
    ((x ∈ Set.range iNewQ) ∧ x ∉ Set.range iNewE) ∨
    ((y ∈ Set.range iNewQ) ∧ y ∉ Set.range iNewE) := by
  classical
  have hCannotBothE :
      ¬ (x ∈ Set.range iNewE ∧ y ∈ Set.range iNewE) := by
    rintro ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩
    have hSeam₁ : g (iNewE e₁) ∈ Seam := by
      rw [he₁]
      exact hxSeam
    have hSeam₂ : g (iNewE e₂) ∈ Seam := by
      rw [he₂]
      exact hySeam
    have hEqualE : g (iNewE e₁) = g (iNewE e₂) := by
      calc
        g (iNewE e₁) = g x := congrArg g he₁
        _ = g y := hEqual
        _ = g (iNewE e₂) := (congrArg g he₂).symm
    have he : e₁ = e₂ :=
      fullNativeReplacement_retainedComplement_seamInjective_of_local
        iOldE iNewE f g Seam hOldLocalInj
        hSameComplement e₁ e₂ hSeam₁ hSeam₂ hEqualE
    apply hDistinct
    calc
      x = iNewE e₁ := he₁.symm
      _ = iNewE e₂ := congrArg iNewE he
      _ = y := he₂
  by_cases hxE : x ∈ Set.range iNewE
  · have hyNotE : y ∉ Set.range iNewE := by
      intro hyE
      exact hCannotBothE ⟨hxE, hyE⟩
    rcases hNewFree.covers y with ⟨q, hq⟩ | ⟨e, he⟩
    · exact Or.inr ⟨⟨q, hq.symm⟩, hyNotE⟩
    · exact False.elim (hyNotE ⟨e, he.symm⟩)
  · rcases hNewFree.covers x with ⟨q, hq⟩ | ⟨e, he⟩
    · exact Or.inl ⟨⟨q, hq.symm⟩, hxE⟩
    · exact False.elim (hxE ⟨e, he.symm⟩)

/-- A sufficient condition for preservation of COMPLETE NEW seam
injectivity. Suppose every replacement-side vertex mapped into Seam
already belongs to the original Q root. Then the FULL new seam
preimage is contained in the unchanged complement; its injectivity
follows from old complement-local seam injectivity.

This does NOT construct root reflection for the actual selected Q:
that remains the concrete Claim 2 obstruction. -/
theorem fullNativeReplacement_newSeamInj_of_local_and_QrootReflection
    {R E Q V W UT : Type}
    {Root : Structure L R}
    {Complement : Structure L E}
    {Replacement : Structure L Q}
    {Old : Structure L V} {New : Structure L W}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (iNewQ : Structure.Embedding Replacement New)
    (qRoot : Structure.Embedding Root Replacement)
    (eRoot : Structure.Embedding Root Complement)
    (hNewFree : Structure.IsFreeAmalgam qRoot eRoot iNewQ iNewE)
    (f : V → UT) (g : W → UT)
    (Seam : Set UT)
    (hOldLocalInj : Set.InjOn f
      (Set.range iOldE ∩ (f ⁻¹' Seam)))
    (hSameComplement : ∀ e : E,
      g (iNewE e) = f (iOldE e))
    (hQReflect : ∀ q : Q, g (iNewQ q) ∈ Seam →
      q ∈ Set.range qRoot) :
    Set.InjOn g (g ⁻¹' Seam) := by
  have hNewSeamInE : ∀ z : W,
      g z ∈ Seam → z ∈ Set.range iNewE := by
    intro z hz
    rcases hNewFree.covers z with ⟨q, hq⟩ | ⟨e, he⟩
    · have hqSeam : g (iNewQ q) ∈ Seam := by
        simpa only [hq] using hz
      obtain ⟨r, hr⟩ := hQReflect q hqSeam
      refine ⟨eRoot r, ?_⟩
      calc
        iNewE (eRoot r) = iNewQ (qRoot r) :=
          ((hNewFree.overlap (qRoot r) (eRoot r)).mpr
            ⟨r, rfl, rfl⟩).symm
        _ = iNewQ q := congrArg iNewQ hr
        _ = z := hq.symm
    · exact ⟨e, he.symm⟩
  intro x hx y hy hEqual
  obtain ⟨e₁, he₁⟩ := hNewSeamInE x hx
  obtain ⟨e₂, he₂⟩ := hNewSeamInE y hy
  have hSeam₁ : g (iNewE e₁) ∈ Seam := by
    rw [he₁]
    exact hx
  have hSeam₂ : g (iNewE e₂) ∈ Seam := by
    rw [he₂]
    exact hy
  have hEqualE : g (iNewE e₁) = g (iNewE e₂) := by
    calc
      g (iNewE e₁) = g x := congrArg g he₁
      _ = g y := hEqual
      _ = g (iNewE e₂) := (congrArg g he₂).symm
  have hEeq : e₁ = e₂ :=
    fullNativeReplacement_retainedComplement_seamInjective_of_local
      iOldE iNewE f g Seam hOldLocalInj hSameComplement
      e₁ e₂ hSeam₁ hSeam₂ hEqualE
  calc
    x = iNewE e₁ := he₁.symm
    _ = iNewE e₂ := congrArg iNewE hEeq
    _ = y := he₂

end AllThoseRamseyClasses.Lifts
