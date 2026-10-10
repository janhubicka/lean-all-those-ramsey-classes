import AllThoseRamseyClasses.Published.LiteralLocalFiniteness
import PartiteConstruction.Ramsey.ClosureEmbeddingRange

/-!
# The concrete matching closure description of the paired-equivalence class

Language: strict order, equivalence E, and symmetric total matching M
contained in E. The closure relation is M, with the one-point root
having E(x,x), no M(x,x), and no x<x. Exactly one M-tuple extends
each embedded root. This is the precise 2019 Definition 2.12/2.13
closure used in the mathematical counterexample, not a surrogate
functional or total-fibre convention.

The stronger repaired theorem is NOT asserted in this module.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The unique vertex of the root satisfies E(x,x); its order and
matching are irreflexive. -/
abbrev mateRoot : RelStructure Lang (Fin 1) where
  rel
    | .lt, _ => False
    | .equiv, _ => True
    | .mate, _ => False

private theorem mateRoot_irreducible : mateRoot.Irreducible := by
  intro a b hab
  exact False.elim (hab (Subsingleton.elim a b))

/-- The closure-rule relation symbol is the matching M. The root
has exactly one vertex and is strictly smaller than its arity two. -/
abbrev mateRule : ClosureRule Lang where
  symbol := .mate
  rootSize := 1
  rootPositive := by decide
  rootStrict := by decide
  root := mateRoot
  rootIrreducible := mateRoot_irreducible

/-- Singleton closure description of the published test class. -/
abbrev mateRules : ClosureDescription Lang := {mateRule}

/-- Every structure in K is U-closed for the actual matching rule.
This is the first nonvacuous class hypothesis of Definition 2.17. -/
theorem pairedClass_isUClosed {V : Type}
    (C : RelStructure Lang V) (hC : pairedClass C) :
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
          · exact hC.lt_irrefl (t 0)
          · exact False.elim
        | equiv =>
          change C.rel .equiv ((fun _ : Fin 1 => t 0) ∘ v) ↔ True
          rw [htuple]
          constructor
          · intro _; trivial
          · intro _; exact hC.equiv.1 (t 0)
        | mate =>
          change C.rel .mate ((fun _ : Fin 1 => t 0) ∘ v) ↔ False
          rw [htuple]
          constructor
          · exact hC.mate_irrefl (t 0)
          · exact False.elim
    }
    refine ⟨e, ?_⟩
    intro i
    fin_cases i
    rfl
  · intro e
    obtain ⟨y, hy, hyUnique⟩ := hC.mate_total (e 0)
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

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
