import AllThoseRamseyClasses.Published.FinitePairedClass
import PartiteConstruction.Ramsey.CompletionTransfer

/-!
# E-path contradiction for any B-copywise completion

This is the final obstruction needed by the arbitrarily long
paired-equivalence witnesses for the COORDINATED 2019 repair.
Assume every consecutive backbone E-link is witnessed by an
induced B-copy carrying a positive E-tuple, and the closing
negative E-link is witnessed by another B-copy.

Every map respecting all B-copies into a target with transitive
E then forces the two backbone endpoints both equivalent
and inequivalent. The proof is uniform in the path length n.

The existence of a finite U-closed source C_n satisfying all
repaired local-completion hypotheses remains a SEPARATE
unproved Lean task, not assumed by this module.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Transitivity propagates E along a chain of arbitrary finite
length, with no order or matching assumptions on the chain. -/
theorem equiv_along_chain
    {W : Type} (Target : RelStructure Lang W)
    (hTarget : pairedClass Target)
    (b : ℕ → W) :
    ∀ n : ℕ,
      (∀ i : ℕ, i < n →
        edge Target .equiv (b i) (b (i + 1))) →
      edge Target .equiv (b 0) (b n) := by
  intro n
  induction n with
  | zero =>
      intro _
      exact hTarget.equiv.refl (b 0)
  | succ n ih =>
      intro hEdges
      have hEarlier : ∀ i : ℕ, i < n →
          edge Target .equiv (b i) (b (i + 1)) := by
        intro i hi
        exact hEdges i (Nat.lt_succ_of_lt hi)
      exact hTarget.equiv.trans (ih hEarlier)
        (hEdges n (Nat.lt_succ_self n))

/-- A positive E edge is witnessed by one induced copy of Base,
while a negative E edge is witnessed by another.
All original negative relation information is important here. -/
def PositiveCopyEdge
    {U V : Type}
    (Base : RelStructure Lang U) (C : RelStructure Lang V)
    (x y : V) : Prop :=
  ∃ (e : Embedding Base C) (a b : U),
    edge Base .equiv a b ∧ e a = x ∧ e b = y

def NegativeCopyEdge
    {U V : Type}
    (Base : RelStructure Lang U) (C : RelStructure Lang V)
    (x y : V) : Prop :=
  ∃ (e : Embedding Base C) (a b : U),
    ¬ edge Base .equiv a b ∧ e a = x ∧ e b = y

/-- The universal obstruction: no single map can preserve each
installed B-copy when its positive E-links form a path and its
closing B-copy forbids equivalence of the endpoints. -/
theorem no_copywise_completion_of_E_cycle
    {U V W : Type}
    (Base : RelStructure Lang U) (C : RelStructure Lang V)
    (Target : RelStructure Lang W) (hTarget : pairedClass Target)
    (n : ℕ) (backbone : ℕ → V)
    (hPath : ∀ i : ℕ, i < n →
      PositiveCopyEdge Base C (backbone i) (backbone (i + 1)))
    (hClosing : NegativeCopyEdge Base C
      (backbone 0) (backbone n))
    (f : V → W)
    (hf : CopywiseCompletion Base C Target f) :
    False := by
  have hPositive (i : ℕ) (hi : i < n) :
      edge Target .equiv (f (backbone i))
        (f (backbone (i + 1))) := by
    obtain ⟨e, a, b, hE, ha, hb⟩ := hPath i hi
    obtain ⟨g, hg⟩ := hf e
    have hPair : g ∘ ![a, b] = ![g a, g b] := by
      funext k
      fin_cases k <;> rfl
    have hGE : edge Target .equiv (g a) (g b) := by
      change Target.rel .equiv ![g a, g b]
      rw [← hPair]
      exact (g.map_rel_iff .equiv ![a, b]).mpr hE
    simpa only [hg a, hg b, ha, hb] using hGE
  have hEnd : edge Target .equiv
      (f (backbone 0)) (f (backbone n)) :=
    equiv_along_chain Target hTarget
      (fun i => f (backbone i)) n hPositive
  obtain ⟨e, a, b, hNotE, ha, hb⟩ := hClosing
  obtain ⟨g, hg⟩ := hf e
  have hPair : g ∘ ![a, b] = ![g a, g b] := by
    funext k
    fin_cases k <;> rfl
  have hGNot : ¬ edge Target .equiv (g a) (g b) := by
    intro hGE
    have hT : Target.rel .equiv (g ∘ ![a, b]) := by
      rw [hPair]
      exact hGE
    exact hNotE ((g.map_rel_iff .equiv ![a, b]).mp hT)
  have hNotEnd : ¬ edge Target .equiv
      (f (backbone 0)) (f (backbone n)) := by
    simpa only [hg a, hg b, ha, hb] using hGNot
  exact hNotEnd hEnd

/-- Class-level version: no target in the paired-equivalence class
can complete such a source relative to all Base-copies. -/
theorem no_K_copywise_completion_of_E_cycle
    {U V : Type}
    (Base : RelStructure Lang U) (C : RelStructure Lang V)
    (n : ℕ) (backbone : ℕ → V)
    (hPath : ∀ i : ℕ, i < n →
      PositiveCopyEdge Base C (backbone i) (backbone (i + 1)))
    (hClosing : NegativeCopyEdge Base C
      (backbone 0) (backbone n)) :
    ¬ HasCopywiseCompletion finitePairedClass Base C := by
  rintro ⟨W, _, Target, hTarget, f, hf⟩
  exact no_copywise_completion_of_E_cycle
    Base C Target hTarget.2 n backbone hPath hClosing f hf

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
