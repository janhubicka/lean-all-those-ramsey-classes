import AllThoseRamseyClasses.Lifts.EHNWeakImageUncoveredRelationInput
import AllThoseRamseyClasses.Lifts.EHNWeakImageUncoveredFunctionInput
import Mathlib.Tactic

/-!
# Track D: automatic old relation-input test coverage at arity at most one

Every nullary/unary input tuple generates a full native function-closed
irreducible test, irrespective of whether its old relation holds. Combine
the previously proved unary-function input coverage with this relation
analogue to discharge BOTH otherwise-explicit input-test cover premises
of the conditional printed tuple-image normalization theorem.

This gives genuine injective source-support-minimal EHN forbidden witnesses
for native unary languages, and for arbitrary-arity TOTAL functions with
nullary/unary relations. It does not prove Claim 2, strong amalgamation,
or any assertion for uncovered higher-arity/partial inputs.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Any original native relation-input tuple of arity zero or one
is contained in an actual FULL irreducible source test. The
test is the input-generated function-closed hull, and no
positivity of this particular relation input is assumed. -/
theorem relationInputCovered_of_arity_le_one
    {V : Type} (A : Structure L V)
    (R : L.RelSymbol)
    (ys : Fin (L.relArity R) → V)
    (hArity : L.relArity R ≤ 1) :
    RelationInputCoveredByFullIrreducibleTest A R ys := by
  classical
  letI : Subsingleton (Fin (L.relArity R)) := ⟨by
    intro i j
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega⟩
  let Discrete : Structure L (Fin (L.relArity R)) := {
    rel := fun _ _ => False
    func := fun _ _ => ∅
  }
  have hDiscrete : Discrete.Irreducible :=
    nativeIrreducible_of_subsingletonCarrier Discrete
  have hWeak : Discrete.IsWeakHomomorphism A ys := by
    constructor
    · intro T xs hRel
      exact False.elim hRel
    · intro G xs y hy
      exact False.elim hy
  have hHull :
      (A.induce (A.functionClosure (Set.range ys))
        (A.functionClosure_isClosed (Set.range ys))).Irreducible :=
    hDiscrete.functionClosure_weakImage hWeak
  let S : Set V := A.functionClosure (Set.range ys)
  have hS : A.IsClosed S :=
    A.functionClosure_isClosed (Set.range ys)
  let E : Structure L S := A.induce S hS
  let inc : Structure.Embedding E A := A.inclusion S hS
  let inputs : Fin (L.relArity R) → S :=
    fun i => ⟨ys i,
      A.subset_functionClosure (Set.range ys) ⟨i, rfl⟩⟩
  exact ⟨S, E, hHull, inc, inputs, fun _ => rfl⟩

/-- In a language whose native relation symbols all have arity
at most one, EVERY original relation input is automatically
covered by a full irreducible source test. -/
theorem relationInputTuplesCovered_of_allRelArity_le_one
    {V : Type} (A : Structure L V)
    (hArity : ∀ R : L.RelSymbol, L.relArity R ≤ 1) :
    RelationInputTuplesCoveredByIrreducibleTests A := by
  intro R xs
  exact relationInputCovered_of_arity_le_one A R xs (hArity R)

/-- Exact printed image-closure yields a source-support-minimal
INJECTIVE EHN forbidden witness for fully nullary/unary native
languages (both relations AND set-valued functions).
This is a true language-restricted injectivization theorem,
not the unrestricted Section 3 or Claim 2 argument. -/
theorem exists_injectiveMinimalForbiddenEHNWitness_of_unaryLanguage
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    (hFuncArity : ∀ G : L.FuncSymbol, L.funcArity G ≤ 1)
    (hRelArity : ∀ R : L.RelSymbol, L.relArity R ≤ 1)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      ∀ w : ForbiddenEHNWitness F Target,
        v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  have hFunctionCover :
      ∀ {V : Type} (Src : Structure L V),
        F Src → FunctionInputTuplesCoveredByIrreducibleTests Src := by
    intro V Src _
    exact functionInputTuplesCovered_of_allFuncArity_le_one
      Src hFuncArity
  have hRelationCover :
      ∀ {V : Type} (Src : Structure L V),
        F Src → RelationInputTuplesCoveredByIrreducibleTests Src := by
    intro V Src _
    exact relationInputTuplesCovered_of_allRelArity_le_one
      Src hRelArity
  exact exists_injectiveMinimalForbiddenEHNWitness_of_bothInputCovers
    F hFiniteF hImage hFunctionCover hRelationCover
    Target AOnly hExists

/-- Arbitrary-arity TOTAL native set-valued functions may replace
the unary-function restriction, provided all native relations
are still nullary/unary on the original language. The original
forbidden family itself must have nonempty function fibres at
EVERY input. This is a source-family assumption, not inferred
from EHN or connectedness. -/
theorem exists_injectiveMinimalForbiddenEHNWitness_of_totalFunctions_unaryRelations
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    (hTotal : ∀ {V : Type} (Src : Structure L V),
      F Src →
      ∀ G : L.FuncSymbol,
        ∀ xs : Fin (L.funcArity G) → V,
          (Src.func G xs).Nonempty)
    (hRelArity : ∀ R : L.RelSymbol, L.relArity R ≤ 1)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      ∀ w : ForbiddenEHNWitness F Target,
        v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  have hFunctionCover :
      ∀ {V : Type} (Src : Structure L V),
        F Src → FunctionInputTuplesCoveredByIrreducibleTests Src := by
    intro V Src hSrc
    exact functionInputTuplesCovered_of_allSourceFunctionsDefined
      Src (hTotal Src hSrc)
  have hRelationCover :
      ∀ {V : Type} (Src : Structure L V),
        F Src → RelationInputTuplesCoveredByIrreducibleTests Src := by
    intro V Src _
    exact relationInputTuplesCovered_of_allRelArity_le_one
      Src hRelArity
  exact exists_injectiveMinimalForbiddenEHNWitness_of_bothInputCovers
    F hFiniteF hImage hFunctionCover hRelationCover
    Target AOnly hExists

end AllThoseRamseyClasses.Lifts
