import PartiteConstruction.Structure.FreeAmalgam

/-!
# A nested full-functional free-amalgam context is function-closed

Suppose a native full free-amalgam diagram has two embedded sides,
both containing the complete common root. Choose FUNCTION-CLOSED
subsets of both sides, each including its complete root image.

Then the UNION of the two image subsets is function-closed in
the ambient amalgam. A cross-side positive function incidence
cannot occur; if an input vertex belongs to both sides it
comes from the common FULL root, which by assumption belongs to
both chosen closed subsets.

This is the elementary native set-valued-function closure fact
needed by the two-root/contextual lift flip: after a proper
B-only sub-piece is replaced by a full root extension Q', the
candidate outer context Q' union the unchanged closed part of
the original outer piece is still function-closed.

There is no claim that this context is connected, is a genuine
minimal-separator geometric piece, or keeps its original FULL
rooted incompatibility class. The theorem does not use a weak
source image quotient and works with arbitrary arities, including
nullary functions.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Two function-closed subsets of the sides of a FULL native
functional free amalgam glue to a function-closed subset of
the whole amalgam, provided both contain ALL common-root
vertices. This is a property of actual full embeddings and
the complete native function-value fibres. -/
theorem fullFreeAmalgam_closed_union_of_closed_sides
    {H A B C : Type v}
    {Root : Structure L H}
    {Left : Structure L A}
    {Right : Structure L B}
    {Whole : Structure L C}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (SL : Set A) (SR : Set B)
    (hSLclosed : Left.IsClosed SL)
    (hSRclosed : Right.IsClosed SR)
    (hRootLeft : ∀ r : H, sL r ∈ SL)
    (hRootRight : ∀ r : H, sR r ∈ SR) :
    Whole.IsClosed (iL '' SL ∪ iR '' SR) := by
  intro F xs hxs z hz
  rcases (hFree.func_iff F xs z).mp hz with
    ⟨a, b, hab, hx, hz⟩ | ⟨a, b, hab, hx, hz⟩
  · have hInputs : ∀ i, a i ∈ SL := by
      intro i
      have hxi : iL (a i) ∈ iL '' SL ∪ iR '' SR := by
        simpa only [hx, Function.comp_apply] using hxs i
      rcases hxi with hxiL | hxiR
      · obtain ⟨v, hv, heq⟩ := hxiL
        have hav : v = a i := iL.injective heq
        exact hav ▸ hv
      · obtain ⟨v, _hv, heq⟩ := hxiR
        obtain ⟨r, hrL, _hrR⟩ :=
          (hFree.overlap (a i) v).mp heq.symm
        rw [hrL]
        exact hRootLeft r
    have hbSL : b ∈ SL := hSLclosed F a hInputs hab
    exact Or.inl ⟨b, hbSL, hz.symm⟩
  · have hInputs : ∀ i, a i ∈ SR := by
      intro i
      have hxi : iR (a i) ∈ iL '' SL ∪ iR '' SR := by
        simpa only [hx, Function.comp_apply] using hxs i
      rcases hxi with hxiL | hxiR
      · obtain ⟨v, _hv, heq⟩ := hxiL
        obtain ⟨r, _hrL, hrR⟩ :=
          (hFree.overlap v (a i)).mp heq
        rw [hrR]
        exact hRootRight r
      · obtain ⟨v, hv, heq⟩ := hxiR
        have hav : v = a i := iR.injective heq
        exact hav ▸ hv
    have hbSR : b ∈ SR := hSRclosed F a hInputs hab
    exact Or.inr ⟨b, hbSR, hz.symm⟩

end AllThoseRamseyClasses.Lifts
