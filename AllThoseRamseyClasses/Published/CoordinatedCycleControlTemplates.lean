import AllThoseRamseyClasses.Published.CoordinatedCycleFixtures
import Mathlib.Tactic

/-!
# Three exact induced copies of fixed B0 inside the control C0

The uniform path gadgets use block-label profiles A,B,D or B,C,D.
The closing gadget uses A,T,C. In all three profiles the first two
matching blocks are E-equivalent and the third is E-inequivalent to
both, as in the fixed six-vertex B0.

This module constructs *genuine induced embeddings*
B0 -> C0 for all three profiles. These are fixed Fin6/Fin10
lemmas; lifting them along the long cycle's block support
is a separate uniform proof obligation.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Fixed B0 pair profiles 0,1,4 (A,B,D). -/
def controlABDFun (x : Fin 6) : Fin 10 :=
  ⟨if x.val < 4 then x.val else x.val + 4, by
    have hx := x.isLt
    split_ifs <;> omega⟩

/-- Fixed B0 pair profiles 1,3,4 (B,C,D). -/
def controlBCDFun (x : Fin 6) : Fin 10 :=
  ⟨if x.val < 2 then x.val + 2 else x.val + 4, by
    have hx := x.isLt
    split_ifs <;> omega⟩

/-- Fixed B0 pair profiles 0,2,3 (A,T,C). -/
def controlATCFun (x : Fin 6) : Fin 10 :=
  ⟨if x.val < 2 then x.val else x.val + 2, by
    have hx := x.isLt
    split_ifs <;> omega⟩

private theorem controlABD_injective : Function.Injective controlABDFun := by
  intro x y h
  have hval := congrArg (fun z : Fin 10 => z.val) h
  change (if x.val < 4 then x.val else x.val + 4) =
      (if y.val < 4 then y.val else y.val + 4) at hval
  apply Fin.ext
  split_ifs at hval <;> omega

private theorem controlBCD_injective : Function.Injective controlBCDFun := by
  intro x y h
  have hval := congrArg (fun z : Fin 10 => z.val) h
  change (if x.val < 2 then x.val + 2 else x.val + 4) =
      (if y.val < 2 then y.val + 2 else y.val + 4) at hval
  apply Fin.ext
  split_ifs at hval <;> omega

private theorem controlATC_injective : Function.Injective controlATCFun := by
  intro x y h
  have hval := congrArg (fun z : Fin 10 => z.val) h
  change (if x.val < 2 then x.val else x.val + 2) =
      (if y.val < 2 then y.val else y.val + 2) at hval
  apply Fin.ext
  split_ifs at hval <;> omega

private theorem controlABD_rel_iff (R : Symbol) (x y : Fin 6) :
    edge CycleControlC0 R (controlABDFun x) (controlABDFun y) ↔
    edge CycleBaseB0 R x y := by
  cases R <;> fin_cases x <;> fin_cases y <;> decide

private theorem controlBCD_rel_iff (R : Symbol) (x y : Fin 6) :
    edge CycleControlC0 R (controlBCDFun x) (controlBCDFun y) ↔
    edge CycleBaseB0 R x y := by
  cases R <;> fin_cases x <;> fin_cases y <;> decide

private theorem controlATC_rel_iff (R : Symbol) (x y : Fin 6) :
    edge CycleControlC0 R (controlATCFun x) (controlATCFun y) ↔
    edge CycleBaseB0 R x y := by
  cases R <;> fin_cases x <;> fin_cases y <;> decide

/-- A,B,D forms an induced six-vertex B0 inside C0. -/
def controlABDEmbedding : Embedding CycleBaseB0 CycleControlC0 where
  toFun := controlABDFun
  injective := controlABD_injective
  map_rel_iff := by
    intro R t
    have htup : t = ![t 0, t 1] := by
      funext i
      fin_cases i <;> rfl
    rw [htup]
    change edge CycleControlC0 R (controlABDFun (t 0)) (controlABDFun (t 1)) ↔
      edge CycleBaseB0 R (t 0) (t 1)
    exact controlABD_rel_iff R (t 0) (t 1)

/-- B,C,D forms an induced six-vertex B0 inside C0. -/
def controlBCDEmbedding : Embedding CycleBaseB0 CycleControlC0 where
  toFun := controlBCDFun
  injective := controlBCD_injective
  map_rel_iff := by
    intro R t
    have htup : t = ![t 0, t 1] := by
      funext i
      fin_cases i <;> rfl
    rw [htup]
    change edge CycleControlC0 R (controlBCDFun (t 0)) (controlBCDFun (t 1)) ↔
      edge CycleBaseB0 R (t 0) (t 1)
    exact controlBCD_rel_iff R (t 0) (t 1)

/-- A,T,C is the induced closing B0 gadget inside C0. -/
def controlATCEmbedding : Embedding CycleBaseB0 CycleControlC0 where
  toFun := controlATCFun
  injective := controlATC_injective
  map_rel_iff := by
    intro R t
    have htup : t = ![t 0, t 1] := by
      funext i
      fin_cases i <;> rfl
    rw [htup]
    change edge CycleControlC0 R (controlATCFun (t 0)) (controlATCFun (t 1)) ↔
      edge CycleBaseB0 R (t 0) (t 1)
    exact controlATC_rel_iff R (t 0) (t 1)

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
