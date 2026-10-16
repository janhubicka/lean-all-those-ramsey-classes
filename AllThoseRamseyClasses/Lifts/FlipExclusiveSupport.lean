import PartiteConstruction.Structure.FreeAmalgam

/-!
# Exact exclusive-side support of a functional forbidden-piece flip

The proof of Lemma `lem:amalgamationstr` in the 2019 manuscript
minimizes the number of vertices of a forbidden witness mapped
to the A-only side of an ambient free amalgam.

When a piece is flipped from A to B, the replacement piece maps
entirely outside the A-only side, and the map on the complementary
piece remains unchanged. The replacement forbidden source is an
ACTUAL full functional free amalgam. Its A-only support therefore
consists EXACTLY of the images of the A-only vertices of the
unchanged complementary piece.

This is a pure map/support consequence of the genuine
`Structure.IsFreeAmalgam` certificate; no new assumptions about
weak homomorphism-embeddings, injectivity of the global flip map
or preservation of complete function fibres are needed.

The support equivalence below is usable to compare cardinalities
of old and new witnesses. The additional STRICT inequality requires
that the removed old piece contained an A-only vertex not in the
unchanged complement; it is a separate finite counting step.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v

variable {L : Language.{u}}
variable {H E F C Z : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E}
variable {Right : Structure L F}
variable {Whole : Structure L C}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- The A-only support of a flip cannot have a vertex outside the
unchanged complementary side once the replacement side maps
entirely outside the A-only target set. -/
theorem flipExclusiveSupport_right_iff
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (p : C → Z) (pRight : F → Z)
    (hRight : ∀ b, p (iR b) = pRight b)
    (AOnly : Set Z)
    (hLeftAvoid : ∀ a : E, p (iL a) ∉ AOnly)
    (z : C) :
    p z ∈ AOnly ↔
      ∃ b : F, z = iR b ∧ pRight b ∈ AOnly := by
  constructor
  · intro hz
    rcases hfree.covers z with ⟨a, ha⟩ | ⟨b, hb⟩
    · exfalso
      rw [ha] at hz
      exact hLeftAvoid a hz
    · refine ⟨b, hb, ?_⟩
      have hpr : pRight b = p z := by
        calc
          pRight b = p (iR b) := (hRight b).symm
          _ = p z := congrArg p hb.symm
      exact hpr ▸ hz
  · rintro ⟨b, hb, hbS⟩
    have hp : p z = pRight b := by
      calc
        p z = p (iR b) := congrArg p hb
        _ = pRight b := hRight b
    exact hp.symm ▸ hbS

/-- The support inside the new forbidden source is literally the
image under the complementary-side FULL embedding of the old
complement's support. This does not rely on an injective flip map. -/
theorem flipExclusiveSupport_set_eq
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (p : C → Z) (pRight : F → Z)
    (hRight : ∀ b, p (iR b) = pRight b)
    (AOnly : Set Z)
    (hLeftAvoid : ∀ a : E, p (iL a) ∉ AOnly) :
    {z : C | p z ∈ AOnly} =
      iR '' {b : F | pRight b ∈ AOnly} := by
  ext z
  constructor
  · intro hz
    obtain ⟨b, hb, hbS⟩ :=
      (flipExclusiveSupport_right_iff hfree p pRight hRight
        AOnly hLeftAvoid z).mp hz
    exact ⟨b, hbS, hb.symm⟩
  · rintro ⟨b, hbS, hb⟩
    exact (flipExclusiveSupport_right_iff hfree p pRight hRight
      AOnly hLeftAvoid z).mpr ⟨b, hb.symm, hbS⟩

/-- The unchanged complementary side parametrizes the new A-only
support bijectively. Different complementary vertices remain
different because its embedding into the forbidden source is FULL. -/
noncomputable def flipExclusiveSupportEquiv
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (p : C → Z) (pRight : F → Z)
    (hRight : ∀ b, p (iR b) = pRight b)
    (AOnly : Set Z)
    (hLeftAvoid : ∀ a : E, p (iL a) ∉ AOnly) :
    {b : F // pRight b ∈ AOnly} ≃
      {z : C // p z ∈ AOnly} := by
  classical
  refine Equiv.ofBijective
    (fun b : {b : F // pRight b ∈ AOnly} =>
      (⟨iR b.1, ?_⟩ : {z : C // p z ∈ AOnly})) ?_
  · rw [hRight]
    exact b.2
  constructor
  · intro a b hab
    apply Subtype.ext
    apply iR.injective
    exact congrArg Subtype.val hab
  · intro z
    obtain ⟨b, hb, hbS⟩ :=
      (flipExclusiveSupport_right_iff hfree p pRight hRight
        AOnly hLeftAvoid z.1).mp z.2
    refine ⟨⟨b, hbS⟩, ?_⟩
    apply Subtype.ext
    exact hb.symm

/-- For finite forbidden sources, the number of A-only vertices
AFTER the flip equals the number in the unchanged complement.
This is an equality of cardinalities of actual vertices, not
of image sets (the weak flip map may have collisions). -/
theorem flipExclusiveSupport_card_eq
    [Finite C] [Finite F]
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (p : C → Z) (pRight : F → Z)
    (hRight : ∀ b, p (iR b) = pRight b)
    (AOnly : Set Z)
    (hLeftAvoid : ∀ a : E, p (iL a) ∉ AOnly) :
    Nat.card {z : C // p z ∈ AOnly} =
      Nat.card {b : F // pRight b ∈ AOnly} := by
  exact Nat.card_congr
    (flipExclusiveSupportEquiv hfree p pRight hRight
      AOnly hLeftAvoid).symm

end AllThoseRamseyClasses.Lifts
