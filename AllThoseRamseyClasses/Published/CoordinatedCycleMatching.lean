import AllThoseRamseyClasses.Published.CoordinatedCycleBlocks
import AllThoseRamseyClasses.Published.MatchingClosure
import Mathlib.Tactic

/-!
# U-closed matching-pair scaffold for the unbounded cycle family

The final long-cycle witnesses are not in K: they have a partial E
relation and only gadget-induced order tuples. Their matching closure
can nevertheless be proved WITHOUT assuming transitivity of E or
totality of the order.

This module separates precisely the four diagonal/total-matching
properties used by the original matching closure proof. It then
supplies a concrete finite scaffold on CycleVertex k consisting only
of the internal matching-block relations. The later full gadget
relation may add positive cross-block E and order tuples while
preserving the hypotheses of this theorem.

Nothing here asserts the all-cutoff completion hypothesis.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The actual matching closure uses only E reflexivity, < and M
irreflexivity, and uniqueness of each M-output. Transitivity of E,
totality of <, and global K-membership are NOT needed. -/
theorem isUClosed_of_reflexive_E_and_total_M
    {V : Type} (C : RelStructure Lang V)
    (hLt : ∀ x, ¬ edge C .lt x x)
    (hE : ∀ x, edge C .equiv x x)
    (hMirr : ∀ x, ¬ edge C .mate x x)
    (hMt : ∀ x, ∃! y, edge C .mate x y) :
    IsUClosed mateRules C := by
  intro rule hrule
  have heq : rule = mateRule := by
    simpa only [mateRules, Set.mem_singleton_iff] using hrule
  subst rule
  constructor
  · intro t ht
    let e : Embedding mateRoot C := {
      toFun := fun _ => t (0 : Fin 2)
      injective := by
        intro a b _
        exact Subsingleton.elim a b
      map_rel_iff := by
        intro R v
        have htuple :
            ((fun _ : Fin 1 => t (0 : Fin 2)) ∘ v) =
              ![t (0 : Fin 2), t (0 : Fin 2)] := by
          funext i
          fin_cases i <;> rfl
        cases R with
        | lt =>
          change C.rel .lt ((fun _ : Fin 1 => t 0) ∘ v) ↔ False
          rw [htuple]
          constructor
          · exact hLt (t 0)
          · exact False.elim
        | equiv =>
          change C.rel .equiv ((fun _ : Fin 1 => t 0) ∘ v) ↔ True
          rw [htuple]
          constructor
          · intro _; trivial
          · intro _; exact hE (t 0)
        | mate =>
          change C.rel .mate ((fun _ : Fin 1 => t 0) ∘ v) ↔ False
          rw [htuple]
          constructor
          · exact hMirr (t 0)
          · exact False.elim
    }
    refine ⟨e, ?_⟩
    intro i
    fin_cases i
    rfl
  · intro e
    obtain ⟨y, hy, hyUnique⟩ := hMt (e 0)
    let t : Fin 2 → V := ![e 0, y]
    refine ⟨t, ?_, ?_⟩
    · constructor
      · change edge C .mate (e 0) y
        exact hy
      · intro i
        fin_cases i
        rfl
    · intro z hz
      funext i
      fin_cases i
      · change z 0 = e 0
        exact hz.2 0
      · change z 1 = y
        have hz0 : z 0 = e 0 := hz.2 0
        have hzMate : edge C .mate (z 0) (z 1) := by
          have hzTuple : z = ![z 0, z 1] := by
            funext i
            fin_cases i <;> rfl
          change C.rel .mate ![z 0, z 1]
          rw [← hzTuple]
          exact hz.1
        rw [hz0] at hzMate
        exact hyUnique (z 1) hzMate

/-- The unbounded cycle carrier has one matching edge per pair of
vertices in the same block, with no fixed points. -/
def cycleMatching (k : ℕ) (x y : CycleVertex k) : Prop :=
  x.1 = y.1 ∧ x.2 ≠ y.2

theorem cycleMatching_total (k : ℕ) :
    ∀ x : CycleVertex k, ∃! y, cycleMatching k x y := by
  rintro ⟨b, t⟩
  fin_cases t
  · refine ⟨(b, 1), ?_, ?_⟩
    · simp [cycleMatching]
    · rintro ⟨b', j⟩ ⟨hb, hj⟩
      change b = b' at hb
      subst b'
      fin_cases j <;> simp_all
  · refine ⟨(b, 0), ?_, ?_⟩
    · simp [cycleMatching]
    · rintro ⟨b', j⟩ ⟨hb, hj⟩
      change b = b' at hb
      subst b'
      fin_cases j <;> simp_all

/-- A U-closed partial structure containing precisely the internal
relations of the matched blocks. This is only a scaffold, NOT C_n. -/
abbrev cyclePairScaffold (k : ℕ) :
    RelStructure Lang (CycleVertex k) where
  rel
    | .lt, t =>
        (t 0).1 = (t 1).1 ∧ (t 0).2.val < (t 1).2.val
    | .equiv, t => (t 0).1 = (t 1).1
    | .mate, t => cycleMatching k (t 0) (t 1)

theorem cyclePairScaffold_isUClosed (k : ℕ) :
    IsUClosed mateRules (cyclePairScaffold k) := by
  apply isUClosed_of_reflexive_E_and_total_M
  · intro x
    change ¬ (x.1 = x.1 ∧ x.2.val < x.2.val)
    omega
  · intro x
    change x.1 = x.1
    rfl
  · intro x
    change ¬ cycleMatching k x x
    intro h
    exact h.2 rfl
  · intro x
    change ∃! y : CycleVertex k, cycleMatching k x y
    exact cycleMatching_total k x

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
