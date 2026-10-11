import AllThoseRamseyClasses.Published.CoordinatedCycleGadgetWitness
import Mathlib.Tactic

/-!
# Backbone graph is an induced long chordless cycle, without triangles

For every k the m=2k+5 backbone blocks have joint support precisely
when equal or adjacent in the length-m path, or when they are
the special first and last closing pair. In particular the
block-interaction graph induced on backbone blocks has no triangles.
This is the key purely arithmetic part of classifying its cliques.

The private gadget blocks will be handled separately to obtain the
full all-cliques-inside-a-gadget theorem. No completion theorem is
asserted or imported.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- On backbone blocks, pairwise gadget-related means adjacent
on the long chordless cycle or literally equal. -/
theorem cycleRelated_backbone_pair
    (k : ℕ) (a b : CycleBlock k)
    (ha : a.val < cycleBackboneCount k)
    (hb : b.val < cycleBackboneCount k)
    (h : cycleRelatedBlocks k a b) :
    a.val = b.val ∨
    a.val + 1 = b.val ∨ b.val + 1 = a.val ∨
    (a.val = 0 ∧ b.val = cycleBackboneCount k - 1) ∨
    (b.val = 0 ∧ a.val = cycleBackboneCount k - 1) := by
  rcases h with hab | ⟨g, hga, hgb⟩
  · left
    exact congrArg Fin.val hab
  · cases g with
    | inl i =>
      change (a.val = i.val ∨ a.val = i.val + 1 ∨
            a = cycleEdgePrivateBlock k i) at hga
      change (b.val = i.val ∨ b.val = i.val + 1 ∨
            b = cycleEdgePrivateBlock k i) at hgb
      have haTwo : a.val = i.val ∨ a.val = i.val + 1 := by
        rcases hga with hx | hx | hx
        · exact Or.inl hx
        · exact Or.inr hx
        · have hv := congrArg (fun z : CycleBlock k => z.val) hx
          change a.val = cycleBackboneCount k + i.val at hv
          omega
      have hbTwo : b.val = i.val ∨ b.val = i.val + 1 := by
        rcases hgb with hx | hx | hx
        · exact Or.inl hx
        · exact Or.inr hx
        · have hv := congrArg (fun z : CycleBlock k => z.val) hx
          change b.val = cycleBackboneCount k + i.val at hv
          omega
      rcases haTwo with hh | hh <;>
        rcases hbTwo with hj | hj <;> omega
    | inr unit =>
      change (a.val = 0 ∨ a.val = cycleBackboneCount k - 1 ∨
            a = cycleClosingPrivateBlock k) at hga
      change (b.val = 0 ∨ b.val = cycleBackboneCount k - 1 ∨
            b = cycleClosingPrivateBlock k) at hgb
      have haTwo : a.val = 0 ∨
          a.val = cycleBackboneCount k - 1 := by
        rcases hga with hx | hx | hx
        · exact Or.inl hx
        · exact Or.inr hx
        · have hv := congrArg (fun z : CycleBlock k => z.val) hx
          change a.val = cycleBlockCount k - 1 at hv
          simp only [cycleBackboneCount, cycleBlockCount] at *
          omega
      have hbTwo : b.val = 0 ∨
          b.val = cycleBackboneCount k - 1 := by
        rcases hgb with hx | hx | hx
        · exact Or.inl hx
        · exact Or.inr hx
        · have hv := congrArg (fun z : CycleBlock k => z.val) hx
          change b.val = cycleBlockCount k - 1 at hv
          simp only [cycleBackboneCount, cycleBlockCount] at *
          omega
      rcases haTwo with hh | hh <;>
        rcases hbTwo with hj | hj <;> omega

/-- An odd backbone cycle of length at least five admits no three
distinct pairwise related backbone blocks. -/
theorem cycleBackbone_no_triangle
    (k : ℕ) (a b c : CycleBlock k)
    (ha : a.val < cycleBackboneCount k)
    (hb : b.val < cycleBackboneCount k)
    (hc : c.val < cycleBackboneCount k)
    (hab : cycleRelatedBlocks k a b)
    (hac : cycleRelatedBlocks k a c)
    (hbc : cycleRelatedBlocks k b c)
    (hDistinct : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    False := by
  have hab' := cycleRelated_backbone_pair k a b ha hb hab
  have hac' := cycleRelated_backbone_pair k a c ha hc hac
  have hbc' := cycleRelated_backbone_pair k b c hb hc hbc
  have habNe : a.val ≠ b.val := by
    intro hv
    exact hDistinct.1 (Fin.ext hv)
  have hacNe : a.val ≠ c.val := by
    intro hv
    exact hDistinct.2.1 (Fin.ext hv)
  have hbcNe : b.val ≠ c.val := by
    intro hv
    exact hDistinct.2.2 (Fin.ext hv)
  have hm : 5 ≤ cycleBackboneCount k := cycleBackboneCount_ge_five k
  omega

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
