import AllThoseRamseyClasses.Lifts.GlobalCountableLiftSignature
import PartiteConstruction.Structure.Relationalize
import Mathlib.ModelTheory.Basic

/-!
# Track F: full native functional graph as a first-order relational structure

Mathlib's `FirstOrder.Language.DirectLimit` operates on models of
`FirstOrder.Language`, while the original Section 3 global lift
uses `StructuralRamsey.Structure` with COMPLETE set-valued
partial functions and full embeddings.

We supply the first, exact, language-level bridge. Each native
relation R of arity n is a first-order n-ary relation; every native
function F of arity n becomes an (n+1)-ary FIRST-ORDER RELATION,
whose truth exactly records membership of a value y in the
entire set-valued fibre F(x_0,...,x_{n-1}). There are NO first-order
function symbols and no replacement of a partial function by a
total one. The existing `Structure.graph` relationalization is
reused verbatim.

Every positive and negative old relation tuple and each entire
old function fibre (including empty/undefined and nullary ones)
are recovered exactly. The countable-signature result for a regular
global piece lift transfers to the first-order graph language.

**IMPORTANT:** An ordinary first-order relational graph embedding
need not have function-closed image. Reconstructing a FULL native
functional embedding still requires the closure condition proved
in `PartiteConstruction/Functional/Closed.lean`.
This module does NOT claim that the first-order age is hereditary
under arbitrary induced subsets, nor that a direct limit or a
Fraïssé limit has been constructed.

The numbered ramsey.tex is frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey

universe u v

/-- Re-index every original relation symbol by its actual arity.
The resulting first-order language has NO total function symbols. -/
def firstOrderRelGraphLanguage
    (R : RelLanguage.{u}) : FirstOrder.Language.{u,u} where
  Functions := fun _ => Empty.{u}
  Relations := fun n => {s : R.Symbol // R.arity s = n}

/-- Exact interpretation of a StructuralRamsey relational structure
in the corresponding functionless FIRST-ORDER language. The cast
only changes the tuple-index type from arity(s) to its chosen index n. -/
def firstOrderRelGraphStructure
    {R : RelLanguage.{u}} {V : Type v}
    (A : RelStructure R V) :
    (firstOrderRelGraphLanguage R).Structure V where
  funMap := fun {_} f _ => isEmptyElim f
  RelMap := fun {_} s xs =>
    A.rel s.1 (fun i => xs (Fin.cast s.2 i))

/-- The first-order relation indexed by s has exactly the original
relation truth value, including repeated coordinates and n=0. -/
theorem firstOrderRelGraph_rel_iff
    {R : RelLanguage.{u}} {V : Type v}
    (A : RelStructure R V)
    (s : R.Symbol)
    (xs : Fin (R.arity s) → V) :
    (firstOrderRelGraphStructure A).RelMap
      (⟨s, rfl⟩ :
        (firstOrderRelGraphLanguage R).Relations (R.arity s)) xs ↔
      A.rel s xs := by
  rfl

/-- The FIRST-ORDER graph language is functionless, exactly as
required to represent partially defined and set-valued functions
by their incidence relations. -/
instance firstOrderRelGraph_isRelational
    (R : RelLanguage.{u}) :
    (firstOrderRelGraphLanguage R).IsRelational := by
  intro n
  change IsEmpty Empty.{u}
  infer_instance

/-- If the original relation-symbol type is countable, its
arity-indexed first-order relation language is countable.
No uniform upper bound on relation arity is required. -/
theorem firstOrderRelGraph_symbols_countable
    (R : RelLanguage.{u}) [Countable R.Symbol] :
    Countable (firstOrderRelGraphLanguage R).Symbols := by
  letI (n : ℕ) :
      Countable ((firstOrderRelGraphLanguage R).Relations n) := by
    change Countable {s : R.Symbol // R.arity s = n}
    infer_instance
  letI (n : ℕ) :
      Countable ((firstOrderRelGraphLanguage R).Functions n) := by
    change Countable Empty.{u}
    infer_instance
  infer_instance

/-- First-order presentation of the EXISTING, exact relational
graph of a native functional structure. Its old functions are
represented by one additional output coordinate; their entire
set-valued interpretation is preserved. -/
def firstOrderNativeGraphStructure
    {L : Language.{u}} {V : Type v}
    (A : Structure L V) :
    (firstOrderRelGraphLanguage L.graph).Structure V :=
  firstOrderRelGraphStructure A.graph

/-- Every old native relation tuple is reflected EXACTLY in the
first-order graph, without changing arities or sign. -/
theorem firstOrderNativeGraph_rel_iff
    {L : Language.{u}} {V : Type v}
    (A : Structure L V)
    (R : L.RelSymbol)
    (xs : Fin (L.relArity R) → V) :
    (firstOrderNativeGraphStructure A).RelMap
      (⟨Sum.inl R, rfl⟩ :
        (firstOrderRelGraphLanguage L.graph).Relations
          (L.relArity R)) xs ↔
      A.rel R xs := by
  rfl

/-- The new first-order (n+1)-ary function-graph relation means
EXACTLY that the displayed output belongs to the old complete
set-valued function fibre, for arbitrary n including n=0. -/
theorem firstOrderNativeGraph_func_iff
    {L : Language.{u}} {V : Type v}
    (A : Structure L V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V)
    (y : V) :
    (firstOrderNativeGraphStructure A).RelMap
      (⟨Sum.inr F, rfl⟩ :
        (firstOrderRelGraphLanguage L.graph).Relations
          (L.funcArity F + 1))
      (Structure.funcTuple xs y) ↔
      y ∈ A.func F xs := by
  change A.graph.rel (.inr F)
    (Structure.funcTuple xs y) ↔ y ∈ A.func F xs
  exact Structure.graph_func_snoc A F xs y

/-- The ENTIRE native function-value SET is reconstructed from
the corresponding first-order graph-incidence predicate. No
unproved totality, output uniqueness, or injectivization
assumptions are introduced. -/
theorem firstOrderNativeGraph_wholeFunctionFibre
    {L : Language.{u}} {V : Type v}
    (A : Structure L V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V) :
    {y : V |
      (firstOrderNativeGraphStructure A).RelMap
        (⟨Sum.inr F, rfl⟩ :
          (firstOrderRelGraphLanguage L.graph).Relations
            (L.funcArity F + 1))
        (Structure.funcTuple xs y)} = A.func F xs := by
  ext y
  exact firstOrderNativeGraph_func_iff A F xs y

/-- The purely relational FIRST-ORDER graph language of any
countable native functional signature is itself countable. -/
theorem firstOrderNativeGraph_symbols_countable
    (L : Language.{u})
    [Countable L.RelSymbol] [Countable L.FuncSymbol] :
    Countable (firstOrderRelGraphLanguage L.graph).Symbols := by
  have hSymbol : Countable L.graph.Symbol := by
    change Countable (L.RelSymbol ⊕ L.FuncSymbol)
    infer_instance
  letI : Countable L.graph.Symbol := hSymbol
  exact firstOrderRelGraph_symbols_countable L.graph

/-- The ACTUAL regular ORIGINAL global piece lift has a countable
first-order graph language whenever the old native symbol types
are finite. This includes infinite regular forbidden-piece
families with new relations of unbounded positive arities. -/
theorem firstOrderOriginalGlobalLift_symbols_countable
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hRegular : GlobalFunctionalPieceRegular F) :
    Countable
      (firstOrderRelGraphLanguage
        (globalFunctionalPieceLanguage F).graph).Symbols := by
  obtain ⟨hRel, hFunc⟩ :=
    globalFunctionalPieceLanguage_countable_of_finiteOld
      F hRegular
  letI : Countable (globalFunctionalPieceLanguage F).RelSymbol :=
    hRel
  letI : Countable (globalFunctionalPieceLanguage F).FuncSymbol :=
    hFunc
  exact firstOrderNativeGraph_symbols_countable
    (globalFunctionalPieceLanguage F)

end AllThoseRamseyClasses.Lifts
