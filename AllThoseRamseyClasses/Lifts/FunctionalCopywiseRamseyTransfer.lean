import PartiteConstruction.Ramsey.FreeAmalgamationFunctionsAllArity

/-!
# Copywise Ramsey transfer for genuine functional structures

The final colouring argument in a functional multiamalgamation proof
needs a map of vertices of a Ramsey control `C` into the completed
object `D` which is a FULL embedding on each copy of `B`.
It need not be a homomorphism on all of `C`, and not every
`A`-copy of `C` must survive.

The assertion below is independent of the chosen function signature,
of the forbidden family, and of any closure notion. All complete
partial/set-valued function fibres are respected on preserved copies
because the resulting maps are `Structure.Embedding`s.

An arbitrary `A`-copy whose vertex map fails to lift receives a
default colour. Inside a preserved `B`-copy all `A`-copies lift,
so the default colour is never used in the final monochromaticity
argument. The nonempty-colour hypothesis is essential for this step.

This is a transfer theorem, NOT an existence theorem for functional
copywise completions or a Ramsey property of a maximal-trace age.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {M : Language.{u}}

/-- An actual functional Ramsey arrow survives a vertex-map
completion which is full on every B-copy. No global embedding of
the Ramsey control C is needed. -/
theorem functionalArrow_of_BCopywiseCompletion
    {VA VB VC VD : Type}
    {A : Structure M VA} {B : Structure M VB}
    {C : Structure M VC} {D : Structure M VD}
    {f : VC → VD} {κ : Type v} [Nonempty κ]
    (hArrow : Structure.Arrow A B C κ)
    (hB : ∀ b : Structure.Embedding B C,
      ∃ bD : Structure.Embedding B D,
        ∀ x : VB, bD x = f (b x)) :
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
  obtain ⟨b, hMono⟩ := hArrow pullColour
  obtain ⟨bD, hbD⟩ := hB b
  have hPull (a : Structure.Embedding A B) :
      pullColour (b.comp a) = χ (bD.comp a) := by
    apply pull_spec
    intro x
    exact hbD (a x)
  refine ⟨bD, ?_⟩
  intro a₁ a₂
  calc
    χ (bD.comp a₁) = pullColour (b.comp a₁) := (hPull a₁).symm
    _ = pullColour (b.comp a₂) := hMono a₁ a₂
    _ = χ (bD.comp a₂) := hPull a₂

end AllThoseRamseyClasses.Lifts
