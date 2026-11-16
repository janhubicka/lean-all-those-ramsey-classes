import AllThoseRamseyClasses.Lifts.EHNWeakImageUncoveredRelationInput
import AllThoseRamseyClasses.Lifts.EHNInputCoverFunctionFibre
import Mathlib.Tactic

/-!
# Actual native crossing-hull certificates when input coverage fails

The printed 2019 original EHN lift argument cannot infer
function-closed or tuple-surjective target ranges from arbitrary
weak maps. The repaired conditional Track C argument uses two
SOURCE-LOCAL requirements on a chosen global lex minimum:

* full irreducible source tests for all native function INPUT tuples;
* positive original relation tuple preimages for every positive
  target relation tuple inside the actual source image range.

Rather than declaring failure of either condition a dead end,
this module produces a FINITE, ACTUAL, native source-geometric
obstruction: some input tuple whose FUNCTION-CLOSED generated
hull has a PROPER FULL free decomposition and whose input
generators cross BOTH sides. No quotient, guessed injectivity
or extra relation/function arity bound is involved.

The relational obstruction also carries its actual positive
target relation and negative source relation at EXACT same
target input coordinates. This is a strong concrete target
for the missing geometrical Claim 2 collision repair.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An individual native function-input tuple is protected by a
FULL irreducible original source test containing every input
coordinate, potentially with additional source vertices. -/
def FunctionInputCoveredByFullIrreducibleTest
    {V : Type} (A : Structure L V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V) : Prop :=
  ∃ (U : Type) (E : Structure L U),
    E.Irreducible ∧
    ∃ (e : Structure.Embedding E A)
      (ys : Fin (L.funcArity F) → U),
      ∀ i, e (ys i) = xs i

/-- If a function input tuple is NOT protected by any FULL
irreducible source test, then its genuinely generated and
function-closed native hull CANNOT itself be irreducible.
Otherwise the hull inclusion would be just such a test. -/
theorem uncoveredFunctionInput_generatedHull_notIrreducible
    {V : Type} (A : Structure L V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V)
    (hUncovered : ¬ FunctionInputCoveredByFullIrreducibleTest A F xs) :
    ¬ (A.induce (A.functionClosure (Set.range xs))
      (A.functionClosure_isClosed (Set.range xs))).Irreducible := by
  intro hIrred
  let S : Set V := A.functionClosure (Set.range xs)
  have hS : A.IsClosed S := A.functionClosure_isClosed (Set.range xs)
  let E : Structure L S := A.induce S hS
  let inc : Structure.Embedding E A := A.inclusion S hS
  let inputs : Fin (L.funcArity F) → S :=
    fun i => ⟨xs i,
      A.subset_functionClosure (Set.range xs) ⟨i, rfl⟩⟩
  apply hUncovered
  exact ⟨S, E, hIrred, inc, inputs, fun _ => rfl⟩

/-- Every uncovered function input has a PROPER native FULL free
decomposition of its function-closed generated hull, and the
original input generators CANNOT all belong to either side.
This is actual functional crossing, not graph disconnection. -/
theorem uncoveredFunctionInput_hasCrossingFreeDecomposition
    {V : Type} (A : Structure L V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V)
    (hUncovered : ¬ FunctionInputCoveredByFullIrreducibleTest A F xs) :
    ∃ d : ProperFreeDecomposition
      (A.induce (A.functionClosure (Set.range xs))
        (A.functionClosure_isClosed (Set.range xs))),
      (¬ ∀ i : Fin (L.funcArity F), ∃ a : d.Left,
        Structure.closureLift A xs i = d.leftIn a) ∧
      (¬ ∀ i : Fin (L.funcArity F), ∃ b : d.Right,
        Structure.closureLift A xs i = d.rightIn b) := by
  have hNotIrred :=
    uncoveredFunctionInput_generatedHull_notIrreducible
      A F xs hUncovered
  have hDecomp : Nonempty (ProperFreeDecomposition
      (A.induce (A.functionClosure (Set.range xs))
        (A.functionClosure_isClosed (Set.range xs)))) := by
    by_contra hNoDecomp
    exact hNotIrred
      ((irreducible_iff_noProperFreeDecomposition
        (A.induce (A.functionClosure (Set.range xs))
          (A.functionClosure_isClosed (Set.range xs)))).mpr
          hNoDecomp)
  obtain ⟨d⟩ := hDecomp
  exact ⟨d, generatedClosedHull_properFreeDecomposition_inputsCross
    A xs d⟩

/-- The NEGATION of the original whole-source native
function-input-test cover yields a concrete uncovered
function-input tuple and a crossed proper FULL free
decomposition of its genuinely function-closed generated hull.

No forbidden-family, target map, or source finite hypothesis
is required for this native geometry fact. -/
theorem missingFunctionInputCover_hasCrossingHull
    {V : Type} (A : Structure L V)
    (hMissing : ¬ FunctionInputTuplesCoveredByIrreducibleTests A) :
    ∃ (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → V),
      ∃ d : ProperFreeDecomposition
        (A.induce (A.functionClosure (Set.range xs))
          (A.functionClosure_isClosed (Set.range xs))),
        (¬ ∀ i : Fin (L.funcArity F), ∃ a : d.Left,
          Structure.closureLift A xs i = d.leftIn a) ∧
        (¬ ∀ i : Fin (L.funcArity F), ∃ b : d.Right,
          Structure.closureLift A xs i = d.rightIn b) := by
  classical
  change ¬ ∀ (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V),
      FunctionInputCoveredByFullIrreducibleTest A F xs at hMissing
  push_neg at hMissing
  obtain ⟨F, xs, hUncovered⟩ := hMissing
  obtain ⟨d, hCross⟩ :=
    uncoveredFunctionInput_hasCrossingFreeDecomposition
      A F xs hUncovered
  exact ⟨F, xs, d, hCross⟩

/-- When a genuine original weak EHN source map FAILS the
positive OLD relation-tuple coverage of its actual range, it
contains a concrete source relation INPUT tuple with:

(1) a POSITIVE native target relation at the exact image tuple;
(2) a NEGATIVE native source relation at the exact source tuple;
(3) an ACTUAL proper FULL free decomposition of the source
    input-generated function-closed hull, and
(4) the source input coordinates CROSS BOTH decomposition sides.

This rules out treating missing relation coverage as an
uninterpreted proof gap, while not yet eliminating such a
crossing by original 2019 canonical-lift hypotheses. -/
theorem ehn_missingRangeRelationCover_hasCrossingHull
    {V W : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (hMissing : ¬ SourceRelationTuplesCoveredOnRange A B f) :
    ∃ (R : L.RelSymbol)
      (xs : Fin (L.relArity R) → V),
      B.rel R (f ∘ xs) ∧
      ¬ A.rel R xs ∧
      ∃ d : ProperFreeDecomposition
        (A.induce (A.functionClosure (Set.range xs))
          (A.functionClosure_isClosed (Set.range xs))),
        (¬ ∀ i : Fin (L.relArity R), ∃ a : d.Left,
          Structure.closureLift A xs i = d.leftIn a) ∧
        (¬ ∀ i : Fin (L.relArity R), ∃ b : d.Right,
          Structure.closureLift A xs i = d.rightIn b) := by
  classical
  have hGap :
      ∃ (R : L.RelSymbol)
        (zs : Fin (L.relArity R) → W),
        (∀ i, zs i ∈ Set.range f) ∧
        B.rel R zs ∧
        (∀ ys : Fin (L.relArity R) → V,
          ¬ (A.rel R ys ∧ zs = f ∘ ys)) := by
    by_contra hNoGap
    apply hMissing
    intro R zs hRange hPositive
    by_contra hNoRel
    apply hNoGap
    refine ⟨R, zs, hRange, hPositive, ?_⟩
    intro ys hWitness
    exact hNoRel ⟨ys, hWitness⟩
  obtain ⟨R, zs, hRange, hPositive, hNoSource⟩ := hGap
  let xs : Fin (L.relArity R) → V :=
    fun i => Classical.choose (hRange i)
  have hCoords : zs = f ∘ xs := by
    funext i
    exact (Classical.choose_spec (hRange i)).symm
  have hTarget : B.rel R (f ∘ xs) := by
    rw [← hCoords]
    exact hPositive
  have hNoRel : ¬ A.rel R xs := by
    intro hRel
    exact hNoSource xs ⟨hRel, hCoords⟩
  have hUncovered :
      ¬ RelationInputCoveredByFullIrreducibleTest A R xs := by
    intro hCover
    have hReflected : A.rel R xs :=
      ehn_localRelationInputCover_reflectsTargetPositive
        A B f hf R xs hCover hTarget
    exact hNoRel hReflected
  obtain ⟨d, hCross⟩ :=
    uncoveredRelationInput_hasCrossingFreeDecomposition
      A R xs hUncovered
  exact ⟨R, xs, hTarget, hNoRel, d, hCross⟩

end AllThoseRamseyClasses.Lifts
