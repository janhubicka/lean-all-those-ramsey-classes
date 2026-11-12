import AllThoseRamseyClasses.Lifts.Claim2ActualOuterStatePersistence

/-!
# Seam collision locality across a genuine full native free-amalgam flip

Suppose the old weak EHN map is injective on the COMPLETE preimage
of the target seam, and a selected-Q source flip retains the exact
old complementary source with the same weak target coordinates.

Then no NEW weak-map seam collision can occur between two vertices
both belonging to the unchanged full native complement: the old
source representatives are distinct only if the new ones are
distinct, and the original seam injection rules out their equal
target images. Therefore every genuine new seam collision contains
a SOURCE vertex OUTSIDE the retained complement; by the actual
full free-amalgam cover, this vertex comes from the replacement side Q.

The theorem does not say that the replacement-side vertex avoids
the seam, nor that the new weak map is globally injective. Its value
is identifying which genuine source side must be inspected in a
future collision-repair argument. No quotient of the weak image
and no image-cardinality accounting is used.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Two surviving source complement vertices which map into the
common target seam cannot collide under the new weak map if the
original weak map was injective on its complete seam preimage. -/
theorem fullNativeReplacement_retainedComplement_seamInjective
    {V W E UT : Type}
    {Old : Structure L V} {New : Structure L W}
    {Complement : Structure L E}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (f : V → UT) (g : W → UT)
    (Seam : Set UT)
    (hOldSeamInj : Set.InjOn f (f ⁻¹' Seam))
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
  exact iOldE.injective
    (hOldSeamInj hOldSeam₁ hOldSeam₂ hOldEq)

/-- A genuinely new collision on the complete common target seam
contains an actual source vertex that is NOT in the unchanged
complement. By full native free-amalgam coverage, that vertex
belongs to the replacement side Q.

In particular, no target-image quotient is being formed: the
two colliding source vertices are returned literally. -/
theorem fullNativeReplacement_newSeamCollision_hits_replacementOutsideComplement
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
    (hOldSeamInj : Set.InjOn f (f ⁻¹' Seam))
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
      fullNativeReplacement_retainedComplement_seamInjective
        iOldE iNewE f g Seam hOldSeamInj
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
    · exact Or.inr ⟨⟨q, hq⟩, hyNotE⟩
    · exact False.elim (hyNotE ⟨e, he⟩)
  · rcases hNewFree.covers x with ⟨q, hq⟩ | ⟨e, he⟩
    · exact Or.inl ⟨⟨q, hq⟩, hxE⟩
    · exact False.elim (hxE ⟨e, he⟩)

end AllThoseRamseyClasses.Lifts
