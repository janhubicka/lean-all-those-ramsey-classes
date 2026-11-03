import AllThoseRamseyClasses.Lifts.FunctionalCopywiseRamseyTransfer

/-!
# Track E: Ramsey transfer protecting marked B-copies inside larger witnesses

The printed lifting-section Ramsey proof first chooses a larger
maximizing witness of B, call it Bbar, and obtains an ambient Ramsey
control C satisfying C -> (Bbar)^A. It does not have to preserve
EVERY B-copy in C when taking its final maximal lift. It suffices to
preserve, for each FULL Bbar-copy, the ONE designated B-copy of Bbar.

This strictly weakens the hypothesis of the generic functional
B-copywise Ramsey-transfer theorem. The vertex map f : C -> D may
fail to preserve all other B-copies in the ambient control, and
can fail to preserve the old relations or function fibres globally.
On the marked B-copy of each Bbar-copy it must be a FULL functional
embedding, including exact set-valued function fibres.

A colouring of A-copies of D pulls back to the A-copies of C that
survive the map, with an arbitrary default colour for the rest.
The ambient monochromatic Bbar-copy yields a monochromatic marked
B-copy in D: every A-copy lying in the marked B-copy is liftable.

This transfer is unconditional, but constructing a control with the
marked Bbar-copy completion property is a separate Ramsey-picture/
native-witness obligation. No arbitrary regular-family theorem is
inferred here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {M : Language.{u}}

/-- A stronger and more useful conclusion from a WEAKER hypothesis
than `functionalArrow_of_BCopywiseCompletion`: only a distinguished
B-copy inside each bigger marked witness Bbar must be fully preserved.

No B-copy in C outside the marked Bbar-copies is required to survive.
No global weak homomorphism of the vertex map is assumed. -/
theorem functionalArrow_of_markedBCopywiseCompletion
    {VA VB VP VC VD : Type}
    {A : Structure M VA} {B : Structure M VB}
    {Bbar : Structure M VP}
    {C : Structure M VC} {D : Structure M VD}
    {f : VC → VD} {κ : Type v} [Nonempty κ]
    (mark : Structure.Embedding B Bbar)
    (hArrow : Structure.Arrow A Bbar C κ)
    (hCopied :
      ∀ t : Structure.Embedding Bbar C,
        ∃ bD : Structure.Embedding B D,
          ∀ x : VB, bD x = f (t (mark x))) :
    Structure.Arrow A B D κ := by
  classical
  intro χ
  let liftable (a : Structure.Embedding A C) : Prop :=
    ∃ d : Structure.Embedding A D, ∀ x : VA, d x = f (a x)
  let pullColour (a : Structure.Embedding A C) : κ :=
    if h : liftable a then χ (Classical.choose h)
    else Classical.choice (inferInstance : Nonempty κ)
  have pull_spec (a : Structure.Embedding A C)
      (d : Structure.Embedding A D)
      (hd : ∀ x : VA, d x = f (a x)) :
      pullColour a = χ d := by
    have ha : liftable a := ⟨d, hd⟩
    have hEq : Classical.choose ha = d := by
      apply Structure.Embedding.ext
      intro x
      exact (Classical.choose_spec ha x).trans (hd x).symm
    change (if h : liftable a then χ (Classical.choose h)
      else Classical.choice (inferInstance : Nonempty κ)) = χ d
    rw [dif_pos ha, hEq]
  obtain ⟨t, hMono⟩ := hArrow pullColour
  obtain ⟨bD, hbD⟩ := hCopied t
  refine ⟨bD, ?_⟩
  intro a₁ a₂
  have pull_on_mark (a : Structure.Embedding A B) :
      pullColour (t.comp (mark.comp a)) =
        χ (bD.comp a) := by
    apply pull_spec
    intro x
    exact hbD (a x)
  calc
    χ (bD.comp a₁) = pullColour (t.comp (mark.comp a₁)) :=
      (pull_on_mark a₁).symm
    _ = pullColour (t.comp (mark.comp a₂)) :=
      hMono (mark.comp a₁) (mark.comp a₂)
    _ = χ (bD.comp a₂) := pull_on_mark a₂

/-- The original B-copywise transfer is recovered by taking the
large marked witness to be B itself and the mark to be the identity.
This confirms that the marked version generalizes the earlier
unmarked statement rather than assuming a different colouring. -/
theorem functionalArrow_of_markedBCopywiseCompletion_self
    {VA VB VC VD : Type}
    {A : Structure M VA} {B : Structure M VB}
    {C : Structure M VC} {D : Structure M VD}
    {f : VC → VD} {κ : Type v} [Nonempty κ]
    (hArrow : Structure.Arrow A B C κ)
    (hCopy :
      ∀ b : Structure.Embedding B C,
        ∃ bD : Structure.Embedding B D,
          ∀ x : VB, bD x = f (b x)) :
    Structure.Arrow A B D κ := by
  apply functionalArrow_of_markedBCopywiseCompletion
    (mark := Structure.Embedding.id B) hArrow
  intro b
  obtain ⟨bD, hb⟩ := hCopy b
  exact ⟨bD, by intro x; exact hb x⟩

end AllThoseRamseyClasses.Lifts
