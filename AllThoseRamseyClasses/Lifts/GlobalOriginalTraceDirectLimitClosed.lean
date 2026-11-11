import AllThoseRamseyClasses.Lifts.GlobalOriginalTraceNativeDirectLimit
import AllThoseRamseyClasses.Lifts.GlobalFiniteTraceChainFibreStability
import Mathlib.ModelTheory.DirectLimit

/-!
# Track F: function-closed finite-stage images in the ACTUAL direct limit

Let M be the native complete set-valued functional structure
decoded from Mathlib's genuine first-order graph direct limit
of the finite original maximal-trace Fraisse chain.

For every finite stage A_m, the canonical first-order graph
embedding u_m : A_m.graph ↪ M.graph has FUNCTION-CLOSED image:
every function output of M over a tuple from u_m(A_m)
already belongs to u_m(A_m) and comes from the exact
complete native function fibre in A_m.

The proof takes a putative limit output y, represents it at
a finite stage i, moves that output and the original input
tuple to a common later stage k, reflects the full graph
relation at k, invokes the MERGED complete-fibre
stability theorem #901 for the FULL map m→k, and descends
the output to stage m. It is the key missing semantic
condition for using #848 to reconstruct FULL native
embeddings into the infinite limit.

There is NO assumption that an arbitrary first-order graph
embedding is automatically full. Nullary functions, undefined
fibres and multivalued output sets all remain valid.

This proof is conditional on the original finite Fraisse-age
input, which in the general reducible case retains the
unproved shadow-free-amalgamation hypothesis. Neither an
unrestricted Ramsey theorem nor ultrahomogeneity is claimed.
The numbered manuscript ramsey.tex remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The canonical first-order graph map out of any stage commutes
with the ACTUAL full finite structural transition to every
later stage. This follows from Mathlib's verified
`FirstOrder.Language.DirectLimit.of_f` law, rather than from
a guessed quotient map equation. -/
theorem globalOriginalTraceFirstOrderLimitIncl_comp
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (m n : ℕ) (hmn : m ≤ n)
    (x : GlobalOriginalTraceStageVertex
      F hInput representatives diagrams m) :
    globalOriginalTraceFirstOrderLimitIncl
      F hInput representatives diagrams n
      ((globalOriginalFiniteTraceChainLE
        F hInput representatives diagrams m n hmn) x) =
    globalOriginalTraceFirstOrderLimitIncl
      F hInput representatives diagrams m x := by
  -- State the cocone law with exactly the transition map used to
  -- construct Mathlib's quotient.  In particular, do not simplify away
  -- the first-order map's projection before applying `of_f`.
  change
    (FirstOrder.Language.DirectLimit.of
      (GlobalOriginalTraceFirstOrderLanguage F) ℕ
      (fun i : ℕ => GlobalOriginalTraceStageVertex
        F hInput representatives diagrams i)
      (fun i j h => globalOriginalTraceStageFirstOrderMap
        F hInput representatives diagrams i j h) n)
      ((globalOriginalTraceStageFirstOrderMap
        F hInput representatives diagrams m n hmn) x) =
    (FirstOrder.Language.DirectLimit.of
      (GlobalOriginalTraceFirstOrderLanguage F) ℕ
      (fun i : ℕ => GlobalOriginalTraceStageVertex
        F hInput representatives diagrams i)
      (fun i j h => globalOriginalTraceStageFirstOrderMap
        F hInput representatives diagrams i j h) m) x
  exact FirstOrder.Language.DirectLimit.of_f
    (L := GlobalOriginalTraceFirstOrderLanguage F)
    (G := fun i : ℕ => GlobalOriginalTraceStageVertex
      F hInput representatives diagrams i)
    (f := fun i j h => globalOriginalTraceStageFirstOrderMap
      F hInput representatives diagrams i j h)
    (hij := hmn) (x := x)

/-- The canonical first-order graph embedding of EVERY
original finite maximal-trace stage has genuinely
function-CLOSED image in the native structure decoded from
the directed limit. Every output over the old image inputs
is the image of some old output. -/
theorem globalOriginalTraceFirstOrderLimitIncl_closedMap
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (m : ℕ) :
    (globalOriginalFiniteTraceChain
      F hInput representatives diagrams m).model.ClosedMap
      (globalOriginalTraceNativeDirectLimitModel
        F hInput representatives diagrams)
      (globalOriginalTraceFirstOrderLimitIncl
        F hInput representatives diagrams m) := by
  classical
  letI (i : ℕ) : (GlobalOriginalTraceFirstOrderLanguage F).Structure
      (GlobalOriginalTraceStageVertex
        F hInput representatives diagrams i) :=
    globalOriginalTraceStageFirstOrderModel
      F hInput representatives diagrams i
  letI : (GlobalOriginalTraceFirstOrderLanguage F).Structure
      (GlobalOriginalTraceFirstOrderDirectLimit
        F hInput representatives diagrams) :=
    globalOriginalTraceFirstOrderLimitModel
      F hInput representatives diagrams
  intro S xs y hy
  let um := globalOriginalTraceFirstOrderLimitIncl
    F hInput representatives diagrams m
  obtain ⟨i, t, hiy₀⟩ :=
    (FirstOrder.Language.DirectLimit.exists_of
      (L := GlobalOriginalTraceFirstOrderLanguage F)
      (G := fun j : ℕ => GlobalOriginalTraceStageVertex
        F hInput representatives diagrams j)
      (f := fun j k h => globalOriginalTraceStageFirstOrderMap
        F hInput representatives diagrams j k h)
      y)
  have hiy :
      globalOriginalTraceFirstOrderLimitIncl
        F hInput representatives diagrams i t = y := by
    exact hiy₀
  let k := max m i
  have hmk : m ≤ k := Nat.le_max_left m i
  have hik : i ≤ k := Nat.le_max_right m i
  let emk := globalOriginalFiniteTraceChainLE
    F hInput representatives diagrams m k hmk
  let eik := globalOriginalFiniteTraceChainLE
    F hInput representatives diagrams i k hik
  let uk := globalOriginalTraceFirstOrderLimitIncl
    F hInput representatives diagrams k
  have hiyK : uk (eik t) = y :=
    (globalOriginalTraceFirstOrderLimitIncl_comp
      F hInput representatives diagrams i k hik t).trans hiy
  have hmkK (z : GlobalOriginalTraceStageVertex
      F hInput representatives diagrams m) :
      uk (emk z) = um z :=
    globalOriginalTraceFirstOrderLimitIncl_comp
      F hInput representatives diagrams m k hmk z
  let sym :
      (GlobalOriginalTraceFirstOrderLanguage F).Relations
        ((globalFunctionalPieceLanguage F).funcArity S + 1) :=
    ⟨Sum.inr S, rfl⟩
  have hGraph :
      (globalOriginalTraceFirstOrderLimitModel
        F hInput representatives diagrams).RelMap sym
        (Structure.funcTuple (um ∘ xs) y) :=
    (globalOriginalTraceNativeDirectLimit_func_iff
      F hInput representatives diagrams S (um ∘ xs) y).mp hy
  have hTuple :
      uk ∘ Structure.funcTuple (emk ∘ xs) (eik t) =
      Structure.funcTuple (um ∘ xs) y := by
    funext a
    refine Fin.lastCases ?_ (fun j => ?_) a
    · simpa only [Function.comp_apply, Structure.funcTuple_last]
        using hiyK
    · simpa only [Function.comp_apply, Structure.funcTuple_castSucc]
        using hmkK (xs j)
  have hGraphK :
      (globalOriginalTraceStageFirstOrderModel
        F hInput representatives diagrams k).RelMap sym
        (Structure.funcTuple (emk ∘ xs) (eik t)) := by
    have hRef :=
      (uk.map_rel sym (Structure.funcTuple (emk ∘ xs) (eik t))).mp
    apply hRef
    rw [hTuple]
    exact hGraph
  have hStageFunc :
      eik t ∈ (globalOriginalFiniteTraceChain
        F hInput representatives diagrams k).model.func S
          (emk ∘ xs) :=
    (firstOrderNativeGraph_func_iff
      (globalOriginalFiniteTraceChain
        F hInput representatives diagrams k).model
      S (emk ∘ xs) (eik t)).mp hGraphK
  obtain ⟨z, hz, hzk⟩ :=
    (globalOriginalFiniteTraceChainLE_fibre_iff
      F hInput representatives diagrams m k hmk
      S xs (eik t)).mp hStageFunc
  refine ⟨z, hz, ?_⟩
  calc
    um z = uk (emk z) := (hmkK z).symm
    _ = uk (eik t) := congrArg uk hzk
    _ = y := hiyK

end AllThoseRamseyClasses.Lifts
