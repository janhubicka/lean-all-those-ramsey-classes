import AllThoseRamseyClasses.Published.CoordinatedBackboneNoTriangles
import AllThoseRamseyClasses.Published.CoordinatedPrivateGadgetLocalization
import Mathlib.Tactic

/-!
# Every block clique of the long E-cycle lies in one B0 gadget

This supplies the precise finite-graph fact needed to turn the
closed-test *pairwise* relation into a SINGLE B0 gadget containing
the entire tested support.

A block is either a backbone block, one of the (m-1) private
path D blocks, or the closing T block. A clique containing a
private block is supported by its unique gadget (proved separately).
For a clique using only backbone blocks, the induced backbone
graph is triangle-free: hence it has at most two vertices, which
are either one vertex (some incident gadget) or two related
vertices (the common gadget witnessing their adjacency).

This file constructs the gadget for ALL cliques, including the
empty and singleton ones. Nothing is assumed about U-completions.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- Every block of C_k is either a backbone block, an edge-private
D block, or the single closing T block. -/
theorem cycleBlock_backbone_or_private (k : ℕ) (b : CycleBlock k) :
    b.val < cycleBackboneCount k ∨
      (∃ i : Fin (cycleBackboneCount k - 1),
        b = cycleEdgePrivateBlock k i) ∨
      b = cycleClosingPrivateBlock k := by
  classical
  by_cases hb : b.val < cycleBackboneCount k
  · exact Or.inl hb
  · by_cases hFinal : b.val = cycleBlockCount k - 1
    · right
      right
      apply Fin.ext
      change b.val = cycleBlockCount k - 1
      exact hFinal
    · right
      left
      have hi : b.val - cycleBackboneCount k <
          cycleBackboneCount k - 1 := by
        have hbLt := b.isLt
        simp only [cycleBackboneCount, cycleBlockCount] at *
        omega
      let i : Fin (cycleBackboneCount k - 1) :=
        ⟨b.val - cycleBackboneCount k, hi⟩
      refine ⟨i, ?_⟩
      apply Fin.ext
      change b.val = cycleBackboneCount k +
        (b.val - cycleBackboneCount k)
      omega

/-- Any backbone block occurs in at least one installed gadget,
including the last block and the degenerate empty-test cases. -/
theorem cycleBackboneBlock_in_some_gadget (k : ℕ)
    (b : CycleBlock k) (hb : b.val < cycleBackboneCount k) :
    ∃ g : CycleGadget k, cycleGadgetContains k g b := by
  by_cases hLast : b.val = cycleBackboneCount k - 1
  · exact ⟨.inr (), Or.inr (Or.inl hLast)⟩
  · have hEdge : b.val < cycleBackboneCount k - 1 := by
      have hm := cycleBackboneCount_ge_five k
      omega
    let i : Fin (cycleBackboneCount k - 1) := ⟨b.val, hEdge⟩
    exact ⟨.inl i, Or.inl rfl⟩

/-- Every clique entirely on backbone blocks lies in a gadget:
the backbone cycle has no triangles and two related distinct
blocks share an installed gadget by definition. -/
theorem cycle_backbone_clique_in_gadget (k : ℕ)
    (S : Set (CycleBlock k))
    (hBackbone : ∀ b ∈ S, b.val < cycleBackboneCount k)
    (hClique : ∀ a ∈ S, ∀ b ∈ S, cycleRelatedBlocks k a b) :
    ∃ g : CycleGadget k,
      ∀ b ∈ S, cycleGadgetContains k g b := by
  classical
  by_cases hNonempty : S.Nonempty
  · obtain ⟨a, ha⟩ := hNonempty
    by_cases hSecond : ∃ b ∈ S, b ≠ a
    · obtain ⟨b, hb, hba⟩ := hSecond
      have hRel := hClique a ha b hb
      rcases hRel with hab | ⟨g, hga, hgb⟩
      · exact False.elim (hba hab.symm)
      · refine ⟨g, ?_⟩
        intro c hc
        by_cases hca : c = a
        · simpa [hca] using hga
        by_cases hcb : c = b
        · simpa [hcb] using hgb
        exact False.elim
          (cycleBackbone_no_triangle k a b c
            (hBackbone a ha) (hBackbone b hb) (hBackbone c hc)
            (hClique a ha b hb)
            (hClique a ha c hc)
            (hClique b hb c hc)
            ⟨hba.symm, hca.symm, hcb.symm⟩)
    · obtain ⟨g, hga⟩ :=
        cycleBackboneBlock_in_some_gadget k a (hBackbone a ha)
      refine ⟨g, ?_⟩
      intro b hb
      have hba : b = a := by
        by_contra hne
        exact hSecond ⟨b, hb, hne⟩
      simpa [hba] using hga
  · have hLen : 0 < cycleBackboneCount k - 1 := by
      have hm := cycleBackboneCount_ge_five k
      omega
    let i : Fin (cycleBackboneCount k - 1) := ⟨0, hLen⟩
    refine ⟨.inl i, ?_⟩
    intro b hb
    exact False.elim (hNonempty ⟨b, hb⟩)

/-- Every clique in the complete block-interaction graph of C_k
is contained in a single installed path or closing gadget.
This is uniform in k and includes empty and singleton cliques. -/
theorem cycle_block_clique_in_gadget (k : ℕ)
    (S : Set (CycleBlock k))
    (hClique : ∀ a ∈ S, ∀ b ∈ S, cycleRelatedBlocks k a b) :
    ∃ g : CycleGadget k,
      ∀ b ∈ S, cycleGadgetContains k g b := by
  classical
  by_cases hPrivate : ∃ b ∈ S, ¬ b.val < cycleBackboneCount k
  · obtain ⟨b, hb, hBeyond⟩ := hPrivate
    rcases cycleBlock_backbone_or_private k b with hBack
      | ⟨i, hEq⟩ | hEq
    · exact False.elim (hBeyond hBack)
    · have hI : cycleEdgePrivateBlock k i ∈ S := by
        rw [← hEq]
        exact hb
      exact ⟨.inl i,
        cycle_path_private_clique_in_gadget k S hClique i hI⟩
    · have hI : cycleClosingPrivateBlock k ∈ S := by
        rw [← hEq]
        exact hb
      exact ⟨.inr (),
        cycle_closing_private_clique_in_gadget k S hClique hI⟩
  · apply cycle_backbone_clique_in_gadget k S
      (fun b hb => ?_) hClique
    by_contra h
    exact hPrivate ⟨b, hb, h⟩

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
