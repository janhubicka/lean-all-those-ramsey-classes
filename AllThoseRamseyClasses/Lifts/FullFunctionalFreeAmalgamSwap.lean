import PartiteConstruction.Structure.FreeAmalgam

/-!
# Symmetry of actual FULL native functional free amalgam diagrams

The original Section 3 geometric flip needs to transport complete
generated neighbourhood boundaries on BOTH sides of the same full
functional source amalgam. The existing verified exterior-component
theorem is stated for the right side. We therefore provide the exact
symmetry operation on all four components of `Structure.IsFreeAmalgam`,
without treating function incidences as ordinary binary graph edges.

This helper preserves original relation tuples, all defined
set-valued function outputs, arbitrary arities and nullary symbols.
It has no forbidden-family or weak-target-map hypotheses.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Swap the sides of a genuine full native functional free amalgam.
The new diagram retains exact carrier coverage, overlap, relation
tuples and all complete native function incidences. -/
theorem fullFunctionalFreeAmalgam_swap
    {H E B W : Type v}
    {Root : Structure L H}
    {Left : Structure L E}
    {Right : Structure L B}
    {Whole : Structure L W}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam sL sR iL iR) :
    Structure.IsFreeAmalgam sR sL iR iL := by
  refine {
    covers := ?_
    overlap := ?_
    rel_iff := ?_
    func_iff := ?_
  }
  · intro w
    rcases hFree.covers w with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact Or.inr ⟨a, ha⟩
    · exact Or.inl ⟨b, hb⟩
  · intro b a
    constructor
    · intro hba
      obtain ⟨r, hrL, hrR⟩ :=
        (hFree.overlap a b).mp hba.symm
      exact ⟨r, hrR, hrL⟩
    · rintro ⟨r, hrR, hrL⟩
      exact ((hFree.overlap a b).mpr ⟨r, hrL, hrR⟩).symm
  · intro R xs
    constructor
    · intro h
      rcases (hFree.rel_iff R xs).mp h with hL | hR
      · exact Or.inr hL
      · exact Or.inl hR
    · intro h
      rcases h with hR | hL
      · exact (hFree.rel_iff R xs).mpr (Or.inr hR)
      · exact (hFree.rel_iff R xs).mpr (Or.inl hL)
  · intro F xs y
    constructor
    · intro h
      rcases (hFree.func_iff F xs y).mp h with hL | hR
      · exact Or.inr hL
      · exact Or.inl hR
    · intro h
      rcases h with hR | hL
      · exact (hFree.func_iff F xs y).mpr (Or.inr hR)
      · exact (hFree.func_iff F xs y).mpr (Or.inl hL)

end AllThoseRamseyClasses.Lifts
