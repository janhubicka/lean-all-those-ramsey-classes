import AllThoseRamseyClasses.Published.CoordinatedCycleBlocks
import Mathlib.Tactic

/-!
# Missing backbone block for every small weak vertex test

The uniform counterexample family has m = 2*k+5 backbone matching
blocks. A weak test S consisting of fewer than m individual vertices
cannot meet all backbone blocks, even if it contains incomplete
matching pairs. This is the cardinal step needed before the
equivalence-path local-completion construction.

The result does NOT assert that the weak induced test has a
K-completion; the transitive-equivalence extension must still
be constructed and checked separately.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- A vertex set strictly smaller than the backbone has an
entire backbone matching block missing from it. -/
theorem cycle_exists_unhit_backbone
    (k : ℕ) (S : Finset (CycleVertex k))
    (hS : S.card < cycleBackboneCount k) :
    ∃ i : Fin (cycleBackboneCount k),
      ∀ v ∈ S, v.1 ≠ cycleBackboneBlock k i := by
  classical
  by_contra hNo
  push_neg at hNo
  let pick : Fin (cycleBackboneCount k) → S := fun i =>
    ⟨Classical.choose (hNo i), (Classical.choose_spec (hNo i)).1⟩
  have hpick (i : Fin (cycleBackboneCount k)) :
      (pick i).val.1 = cycleBackboneBlock k i :=
    (Classical.choose_spec (hNo i)).2
  have hinj : Function.Injective pick := by
    intro i j hij
    apply cycleBackboneBlock_injective k
    calc
      cycleBackboneBlock k i = (pick i).val.1 := (hpick i).symm
      _ = (pick j).val.1 := congrArg (fun v : S => v.val.1) hij
      _ = cycleBackboneBlock k j := hpick j
  have hCard : cycleBackboneCount k ≤ S.card := by
    simpa using Fintype.card_le_of_injective pick hinj
  omega

/-- For any vertex cutoff n, the concrete backbone with parameter
k=n necessarily misses at least one block on every test of size <= n.
This applies to exact weak tests, not just U-closed tests. -/
theorem cycle_cutoff_tests_miss_backbone
    (n : ℕ) (S : Finset (CycleVertex n))
    (hS : S.card ≤ n) :
    ∃ i : Fin (cycleBackboneCount n),
      ∀ v ∈ S, v.1 ≠ cycleBackboneBlock n i := by
  apply cycle_exists_unhit_backbone n S
  have hn : n < cycleBackboneCount n := by
    simp only [cycleBackboneCount]
    omega
  omega

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
