import AllThoseRamseyClasses.Lifts.EHNWeakSideFullReflectionDefect
import AllThoseRamseyClasses.Lifts.EHNInputTestCoverageClosedRange
import AllThoseRamseyClasses.Lifts.EHNInputCoverFunctionFibre
import AllThoseRamseyClasses.Lifts.EHNWeakImageFullFunctionFibre
import Mathlib.Tactic

/-!
# Track D: a function-fibre defect identifies an uncovered original input tuple

The exact original EHN irreducible-test clause is LOCAL.
Given an original source function-input tuple xs contained in
one FULL irreducible source test, all target function values at
f ∘ xs must be images of actual source function values.

Suppose a bad FULL irreducible test E of the generated weak
quotient Q is weakly factored into a full target side. If the
side has an extra function value at some E-input tuple, then
NO original-source tuple in the appropriate quotient-coordinate
fibre is covered by any full irreducible test of the original
source. Otherwise the original EHN map would lift that value,
the generated quotient would contain it, and the full embedding
E ↪ Q would reflect it into E, contradiction.

This improves the previously conditional global function-input
coverage reduction: under the printed assumptions ALONE, a bad
quotient test entails EITHER an extra positive relation in one
side OR an extra function value whose source input coordinates
are entirely UNPROTECTED by source irreducible tests.

It does not assert that maximal-lift compatibility excludes
such a source tuple. That remains the open root/collision gate.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A SINGLE source native function-input tuple is contained in
some genuinely FULL irreducible source test. This is the local
counterpart of the global `FunctionInputTuplesCoveredByIrreducibleTests`
predicate, with no assumption on any OTHER input tuple. -/
def FunctionInputCoveredByFullIrreducibleTest
    {V : Type} (A : Structure L V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V) : Prop :=
  ∃ (U : Type) (E : Structure L U),
    E.Irreducible ∧
    ∃ (e : Structure.Embedding E A)
      (ys : Fin (L.funcArity F) → U),
      ∀ i, e (ys i) = xs i

/-- A local full irreducible input test suffices to lift EACH
target native function output on that particular input tuple
back into a positive original-source function incidence.
No global input cover or closed target range is required. -/
theorem ehn_localFunctionInputCover_liftsTargetOutput
    {V W : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V)
    (hCovered : FunctionInputCoveredByFullIrreducibleTest A F xs)
    (z : W) (hz : z ∈ B.func F (f ∘ xs)) :
    z ∈ imageSet f (A.func F xs) := by
  classical
  obtain ⟨U, E, hIrr, e, ys, hys⟩ := hCovered
  obtain ⟨g, hg⟩ := hf.2 E hIrr e
  have hArgs : g ∘ ys = f ∘ xs := by
    funext i
    calc
      g (ys i) = f (e (ys i)) := hg (ys i)
      _ = f (xs i) := congrArg f (hys i)
  have hTarget : z ∈ B.func F (g ∘ ys) := by
    rw [hArgs]
    exact hz
  have hInE : z ∈ imageSet g (E.func F ys) := by
    rw [g.map_func F ys]
    exact hTarget
  obtain ⟨v, hv, hgv⟩ := hInE
  have hEImage : e v ∈ imageSet e (E.func F ys) :=
    ⟨v, hv, rfl⟩
  rw [e.map_func F ys] at hEImage
  have hSourceArgs : e ∘ ys = xs := by
    funext i
    exact hys i
  rw [hSourceArgs] at hEImage
  exact ⟨e v, hEImage, (hg v).symm.trans hgv⟩

/-- If a side-local full quotient test is missing a target
function value, then EVERY source input tuple whose coordinates
map to that test tuple lacks a full irreducible source test.

The true source-generated weak image is used, so an original
positive function incidence would generate the target value
inside Q; fullness of E ↪ Q would then force it into E. -/
theorem weakImageFullTest_sideExtraFunction_forcesUncoveredSourceInput
    {V W U US : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (E : Structure L U)
    (e : Structure.Embedding E (Structure.weakImage A B f))
    (Side : Structure L US)
    (j : Structure.Embedding Side B)
    (g : U → US)
    (hCoords : ∀ x : U, j (g x) = (e x).1)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → U)
    (z : US)
    (hSideValue : z ∈ Side.func F (g ∘ xs))
    (hNotSourceTestValue : z ∉ imageSet g (E.func F xs))
    (ys : Fin (L.funcArity F) → V)
    (hInputCoords : ∀ i, f (ys i) = (e (xs i)).1) :
    ¬ FunctionInputCoveredByFullIrreducibleTest A F ys := by
  intro hCovered
  have hSideB : j z ∈ B.func F (j ∘ (g ∘ xs)) := by
    have hImg : j z ∈ imageSet j (Side.func F (g ∘ xs)) :=
      ⟨z, hSideValue, rfl⟩
    rw [j.map_func F (g ∘ xs)] at hImg
    exact hImg
  have hArgs : f ∘ ys = j ∘ (g ∘ xs) := by
    funext i
    calc
      f (ys i) = (e (xs i)).1 := hInputCoords i
      _ = j (g (xs i)) := (hCoords (xs i)).symm
  have hTarget : j z ∈ B.func F (f ∘ ys) := by
    rw [hArgs]
    exact hSideB
  obtain ⟨v, hv, hvz⟩ :
      ∃ v : V, v ∈ A.func F ys ∧ f v = j z :=
    ehn_localFunctionInputCover_liftsTargetOutput
      A B f hf F ys hCovered (j z) hTarget
  let qv : Set.range f := ⟨f v, ⟨v, rfl⟩⟩
  have hQuotient :
      qv ∈ (Structure.weakImage A B f).func F (e ∘ xs) := by
    change ∃ (args : Fin (L.funcArity F) → V) (out : V),
      out ∈ A.func F args ∧
      (∀ i, (e ∘ xs) i =
        (⟨f (args i), ⟨args i, rfl⟩⟩ : Set.range f)) ∧
      qv = ⟨f out, ⟨out, rfl⟩⟩
    refine ⟨ys, v, hv, ?_, rfl⟩
    intro i
    exact Subtype.ext (hInputCoords i).symm
  have hEImage : qv ∈ imageSet e (E.func F xs) := by
    rw [e.map_func F xs]
    exact hQuotient
  obtain ⟨u, hu, hue⟩ := hEImage
  have hgu : g u = z := by
    apply j.injective
    calc
      j (g u) = (e u).1 := hCoords u
      _ = qv.1 := congrArg Subtype.val hue
      _ = j z := hvz
  exact hNotSourceTestValue ⟨u, hu, hgu⟩

/-- If a particular original source function-input tuple
is NOT contained in any full irreducible test, then its
ACTUAL function-closed generated hull in the source cannot
be irreducible. Otherwise the FULL inclusion of that
hull into the source would itself protect the input tuple.

This connects local weak-image fibre surplus to a genuinely
REDUCIBLE native generated closed input structure. -/
theorem uncoveredFunctionInput_generatedClosedHull_notIrreducible
    {V : Type} (A : Structure L V)
    (F : L.FuncSymbol)
    (ys : Fin (L.funcArity F) → V)
    (hUncovered :
      ¬ FunctionInputCoveredByFullIrreducibleTest A F ys) :
    ¬ (A.induce (A.functionClosure (Set.range ys))
       (A.functionClosure_isClosed (Set.range ys))).Irreducible := by
  intro hIrr
  let S : Set V := A.functionClosure (Set.range ys)
  have hS : A.IsClosed S :=
    A.functionClosure_isClosed (Set.range ys)
  let E : Structure L S := A.induce S hS
  let inc : Structure.Embedding E A := A.inclusion S hS
  let inputs : Fin (L.funcArity F) → S :=
    fun i => ⟨ys i,
      A.subset_functionClosure
        (Set.range ys) ⟨i, rfl⟩⟩
  apply hUncovered
  exact ⟨S, E, hIrr, inc, inputs, fun _ => rfl⟩

/-- The locally uncovered function-input tuple gives a GENUINE
proper FULL native free decomposition of its generated
function-closed hull. This is the actual free-amalgamation
notion, not just graph disconnectedness or a missing clique. -/
theorem uncoveredFunctionInput_generatedClosedHull_decomposes
    {V : Type} (A : Structure L V)
    (F : L.FuncSymbol)
    (ys : Fin (L.funcArity F) → V)
    (hUncovered :
      ¬ FunctionInputCoveredByFullIrreducibleTest A F ys) :
    Nonempty (ProperFreeDecomposition
      (A.induce (A.functionClosure (Set.range ys))
        (A.functionClosure_isClosed (Set.range ys)))) := by
  have hNotIrr :=
    uncoveredFunctionInput_generatedClosedHull_notIrreducible
      A F ys hUncovered
  by_contra hNoDecomposition
  exact hNotIrr
    ((irreducible_iff_noProperFreeDecomposition
      (A.induce (A.functionClosure (Set.range ys))
        (A.functionClosure_isClosed (Set.range ys)))).mpr
       hNoDecomposition)

/-- A target-side function-fibre surplus of a FULL quotient
test forces a proper native full free decomposition of the
generated closed hull of EVERY original source input tuple
with the indicated target coordinates. The hypothesis is
only a single side value, not global input-test coverage. -/
theorem weakImageFullTest_sideExtraFunction_forcesSourceInputDecomposition
    {V W U US : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (E : Structure L U)
    (e : Structure.Embedding E (Structure.weakImage A B f))
    (Side : Structure L US)
    (j : Structure.Embedding Side B)
    (g : U → US)
    (hCoords : ∀ x : U, j (g x) = (e x).1)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → U)
    (z : US)
    (hSideValue : z ∈ Side.func F (g ∘ xs))
    (hNotSourceTestValue : z ∉ imageSet g (E.func F xs))
    (ys : Fin (L.funcArity F) → V)
    (hInputCoords : ∀ i, f (ys i) = (e (xs i)).1) :
    Nonempty (ProperFreeDecomposition
      (A.induce (A.functionClosure (Set.range ys))
        (A.functionClosure_isClosed (Set.range ys)))) := by
  exact uncoveredFunctionInput_generatedClosedHull_decomposes A F ys
    (weakImageFullTest_sideExtraFunction_forcesUncoveredSourceInput
      A B f hf E e Side j g hCoords
      F xs z hSideValue hNotSourceTestValue ys hInputCoords)

/-- A full native structure with at most ONE carrier vertex
is irreducible: any genuine free amalgam covering its full
embedded image must put the whole image on one side. This
works with arbitrary nullary operations and relations. -/
theorem nativeIrreducible_of_subsingletonCarrier
    {V : Type} [Subsingleton V]
    (A : Structure L V) : A.Irreducible := by
  intro H E F C Dsrc Esrc Fsrc Csrc sE sF iE iF hFree e
  by_cases hNonempty : Nonempty V
  · obtain ⟨v⟩ := hNonempty
    rcases hFree.covers (e v) with hLeft | hRight
    · obtain ⟨a, ha⟩ := hLeft
      left
      intro x
      refine ⟨a, ?_⟩
      have hx : x = v := Subsingleton.elim x v
      rw [hx]
      exact ha
    · obtain ⟨b, hb⟩ := hRight
      right
      intro x
      refine ⟨b, ?_⟩
      have hx : x = v := Subsingleton.elim x v
      rw [hx]
      exact hb
  · left
    intro x
    exact False.elim (hNonempty ⟨x⟩)

/-- Every native function-input tuple of length 0 or 1
automatically belongs to a FULL irreducible source test.

Its true function-closed generated hull is irreducible: it is
the closed hull of a WEAK image of the empty-incidence
structure on at most one vertex. This uses the pinned
generated-weak-image irreducibility theorem, not a
relational clique approximation or an assumption that
the input tuple is function-defined. -/
theorem functionInputCovered_of_arity_le_one
    {V : Type} (A : Structure L V)
    (F : L.FuncSymbol)
    (ys : Fin (L.funcArity F) → V)
    (hArity : L.funcArity F ≤ 1) :
    FunctionInputCoveredByFullIrreducibleTest A F ys := by
  classical
  letI : Subsingleton (Fin (L.funcArity F)) := ⟨by
    intro i j
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega⟩
  let Discrete : Structure L (Fin (L.funcArity F)) := {
    rel := fun _ _ => False
    func := fun _ _ => ∅
  }
  have hDiscrete : Discrete.Irreducible :=
    nativeIrreducible_of_subsingletonCarrier Discrete
  have hWeak : Discrete.IsWeakHomomorphism A ys := by
    constructor
    · intro R xs hRel
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
  let inc : Structure.Embedding E A :=
    A.inclusion S hS
  let inputs : Fin (L.funcArity F) → S :=
    fun i => ⟨ys i,
      A.subset_functionClosure (Set.range ys) ⟨i, rfl⟩⟩
  exact ⟨S, E, hHull, inc, inputs, fun _ => rfl⟩

/-- For ANY native function arity, a genuinely POSITIVE
source function application generates an irreducible
function-closed full hull. In every full free decomposition
of that hull, the positive F-incidence puts ALL input
coordinates on one side; closure of that side then contains
the entire input-generated hull.

The statement is independent of relations, function-output
multiplicity, finite carriers and any forbidden family. -/
theorem functionGeneratedHull_irreducible_of_positiveInput
    {V : Type} (A : Structure L V)
    (F : L.FuncSymbol)
    (ys : Fin (L.funcArity F) → V)
    (hDefined : (A.func F ys).Nonempty) :
    (A.induce (A.functionClosure (Set.range ys))
      (A.functionClosure_isClosed (Set.range ys))).Irreducible := by
  classical
  let S : Set V := A.functionClosure (Set.range ys)
  have hS : A.IsClosed S :=
    A.functionClosure_isClosed (Set.range ys)
  let H : Structure L S := A.induce S hS
  let inputs : Fin (L.funcArity F) → S :=
    Structure.closureLift A ys
  have hGen : H.Generates inputs :=
    Structure.closureLift_generates A ys
  obtain ⟨v, hv⟩ := hDefined
  have hInS : v ∈ S := hS F ys
    (fun i => A.subset_functionClosure
      (Set.range ys) ⟨i, rfl⟩) hv
  let out : S := ⟨v, hInS⟩
  have hHFn : out ∈ H.func F inputs := by
    exact hv
  intro UX UA UB UT Root Left Right Whole sL sR jL jR
    hFree e
  have hTarget :
      e out ∈ Whole.func F (e ∘ inputs) := by
    have hImg : e out ∈ imageSet e (H.func F inputs) :=
      ⟨out, hHFn, rfl⟩
    rw [e.map_func F inputs] at hImg
    exact hImg
  rcases (hFree.func_iff F (e ∘ inputs) (e out)).mp hTarget with
      ⟨args, _, _, hArgs, _⟩ |
      ⟨args, _, _, hArgs, _⟩
  · left
    have hClosed :
        H.IsClosed {x : S | e x ∈ Set.range jL} :=
      e.preimage_isClosed (Set.range jL) jL.range_isClosed
    have hInputSide : ∀ i, e (inputs i) ∈ Set.range jL := by
      intro i
      exact ⟨args i, (congrFun hArgs i).symm⟩
    exact hGen _ hClosed hInputSide
  · right
    have hClosed :
        H.IsClosed {x : S | e x ∈ Set.range jR} :=
      e.preimage_isClosed (Set.range jR) jR.range_isClosed
    have hInputSide : ∀ i, e (inputs i) ∈ Set.range jR := by
      intro i
      exact ⟨args i, (congrFun hArgs i).symm⟩
    exact hGen _ hClosed hInputSide

/-- Every DEFINED original native function-input tuple,
regardless of arity, belongs to the full irreducible
source test consisting of its input-generated closed hull.

Consequently a locally unprotected input tuple in the
Track D weak-image fibre obstruction can only arise from
an UNDEFINED original function application. -/
theorem functionInputCovered_of_positiveSourceFunctionValue
    {V : Type} (A : Structure L V)
    (F : L.FuncSymbol)
    (ys : Fin (L.funcArity F) → V)
    (hDefined : (A.func F ys).Nonempty) :
    FunctionInputCoveredByFullIrreducibleTest A F ys := by
  let S : Set V := A.functionClosure (Set.range ys)
  have hS : A.IsClosed S :=
    A.functionClosure_isClosed (Set.range ys)
  let H : Structure L S := A.induce S hS
  let inc : Structure.Embedding H A :=
    A.inclusion S hS
  let inputs : Fin (L.funcArity F) → S :=
    Structure.closureLift A ys
  exact ⟨S, H,
    functionGeneratedHull_irreducible_of_positiveInput
      A F ys hDefined,
    inc, inputs, fun _ => rfl⟩

/-- If every native function application in an actual
source structure is DEFINED (has nonempty value fibre),
then every function-input tuple has a full irreducible
source test, regardless of the function arities.

This follows from positive-incidence generated-hull
irreducibility, not from any global injectivity or
partial-operation reflection assumption. -/
theorem functionInputTuplesCovered_of_allSourceFunctionsDefined
    {V : Type} (A : Structure L V)
    (hTotal : ∀ G : L.FuncSymbol,
      ∀ xs : Fin (L.funcArity G) → V,
        (A.func G xs).Nonempty) :
    FunctionInputTuplesCoveredByIrreducibleTests A := by
  intro G xs
  exact functionInputCovered_of_positiveSourceFunctionValue
    A G xs (hTotal G xs)

/-- An original input tuple that is NOT protected by a full
irreducible source test has EMPTY native function-value
fibre at those precise arguments, for any function arity.

This is the exact partial-function definedness meaning of
the local uncovered-input obstruction. -/
theorem uncoveredFunctionInput_sourceFibre_empty
    {V : Type} (A : Structure L V)
    (F : L.FuncSymbol)
    (ys : Fin (L.funcArity F) → V)
    (hUncovered :
      ¬ FunctionInputCoveredByFullIrreducibleTest A F ys) :
    A.func F ys = ∅ := by
  ext z
  constructor
  · intro hz
    exact False.elim
      (hUncovered
        (functionInputCovered_of_positiveSourceFunctionValue
          A F ys ⟨z, hz⟩))
  · intro hz
    exact False.elim hz

/-- In the actual FULL weak quotient-test setting, an extra
target side function value can occur ONLY when the original
F application is UNDEFINED at EVERY source input tuple with
those quotient coordinates. The source function fibre must
be empty, not merely missing that particular target output. -/
theorem weakImageFullTest_sideExtraFunction_allSourceInputsUndefined
    {V W U US : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (E : Structure L U)
    (e : Structure.Embedding E (Structure.weakImage A B f))
    (Side : Structure L US)
    (j : Structure.Embedding Side B)
    (g : U → US)
    (hCoords : ∀ x : U, j (g x) = (e x).1)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → U)
    (z : US)
    (hSideValue : z ∈ Side.func F (g ∘ xs))
    (hNotSourceTestValue : z ∉ imageSet g (E.func F xs))
    (ys : Fin (L.funcArity F) → V)
    (hInputCoords : ∀ i, f (ys i) = (e (xs i)).1) :
    A.func F ys = ∅ := by
  exact uncoveredFunctionInput_sourceFibre_empty A F ys
    (weakImageFullTest_sideExtraFunction_forcesUncoveredSourceInput
      A B f hf E e Side j g hCoords
      F xs z hSideValue hNotSourceTestValue ys hInputCoords)

/-- A target-side EXTRA function value at a full
generated-quotient test forces the corresponding original
TEST function application itself to be UNDEFINED: its
entire native source-test fibre is EMPTY.

Indeed every positive test function value would have a
positive original-source incidence in the generated
quotient, but each original source input tuple with
those coordinates was proved undefined. -/
theorem weakImageFullTest_sideExtraFunction_testFibreEmpty
    {V W U US : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (E : Structure L U)
    (e : Structure.Embedding E (Structure.weakImage A B f))
    (Side : Structure L US)
    (j : Structure.Embedding Side B)
    (g : U → US)
    (hCoords : ∀ x : U, j (g x) = (e x).1)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → U)
    (z : US)
    (hSideValue : z ∈ Side.func F (g ∘ xs))
    (hMissing : z ∉ imageSet g (E.func F xs)) :
    E.func F xs = ∅ := by
  ext out
  constructor
  · intro hPositive
    have hQ :
        e out ∈ (Structure.weakImage A B f).func F (e ∘ xs) := by
      have hImg : e out ∈ imageSet e (E.func F xs) :=
        ⟨out, hPositive, rfl⟩
      rw [e.map_func F xs] at hImg
      exact hImg
    obtain ⟨ys, v, hv, hArgs, _⟩ := hQ
    have hInputCoords :
        ∀ i, f (ys i) = (e (xs i)).1 := by
      intro i
      exact (congrArg Subtype.val (hArgs i)).symm
    have hEmpty :=
      weakImageFullTest_sideExtraFunction_allSourceInputsUndefined
        A B f hf E e Side j g hCoords
        F xs z hSideValue hMissing ys hInputCoords
    have hNot : v ∉ A.func F ys := by
      rw [hEmpty]
      exact Set.not_mem_empty v
    exact False.elim (hNot hv)
  · intro h
    exact False.elim h

/-- In a language whose native function symbols are all nullary
or unary, EVERY original-source function-input tuple has
a FULL irreducible test; the global input-test cover used
elsewhere in Track D becomes a theorem, not an assumption. -/
theorem functionInputTuplesCovered_of_allFuncArity_le_one
    {V : Type} (A : Structure L V)
    (hArity : ∀ F : L.FuncSymbol, L.funcArity F ≤ 1) :
    FunctionInputTuplesCoveredByIrreducibleTests A := by
  intro F ys
  exact functionInputCovered_of_arity_le_one
    A F ys (hArity F)

/-- In the nullary/unary native-function case, a FULL test of
the source-generated quotient cannot have an EXTRA target-side
function value at its prescribed weak coordinates. This
eliminates that branch of the general Track D bad-test
dichotomy without a global source-cover hypothesis. -/
theorem weakImageFullTest_sideExtraFunction_impossible_of_unaryFunctions
    {V W U US : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (hArity : ∀ F : L.FuncSymbol, L.funcArity F ≤ 1)
    (E : Structure L U)
    (e : Structure.Embedding E (Structure.weakImage A B f))
    (Side : Structure L US)
    (j : Structure.Embedding Side B)
    (g : U → US)
    (hCoords : ∀ x : U, j (g x) = (e x).1)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → U)
    (z : US)
    (hSideValue : z ∈ Side.func F (g ∘ xs))
    (hNotSourceTestValue : z ∉ imageSet g (E.func F xs)) :
    False := by
  exact
    (weakImageFullCopy_side_noExtraFunctionFibres_of_sourceInputTests
      A B f hf
      (functionInputTuplesCovered_of_allFuncArity_le_one A hArity)
      E e Side j g hCoords)
      ⟨F, xs, z, hSideValue, hNotSourceTestValue⟩

/-- A bad FULL quotient test in an actual full target free
amalgam therefore yields a SIDE relation surplus, OR a
function-fibre surplus whose input coordinates have NO
irreducibly covered original source preimage tuple.

Unlike the global function-input-cover theorem, this
unconditional structural dichotomy does not assume an
additional source cover predicate. It preserves the exact
forbidden quotient copy, its irreducible test, source
nonlifting certificate and genuine side-map coordinates. -/
theorem badForbiddenWeakImageTest_hasRelationOrUncoveredFunctionInput
    (F : ∀ {X : Type}, Structure L X → Prop)
    {UX UA UB UT : Type}
    (Root : Structure L UX)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (sL : Structure.Embedding Root Left)
    (sR : Structure.Embedding Root Right)
    (jL : Structure.Embedding Left Target)
    (jR : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam sL sR jL jR)
    (w : ForbiddenEHNWitness F Target)
    (hBad : HasForbiddenWeakImageBadIrreducibleTest F Target w) :
    ∃ (Z : Type) (P : Structure L Z),
      F P ∧
      ∃ (e : Structure.Embedding P
        (Structure.weakImage w.source Target w.toTarget))
        (U : Type) (E : Structure L U),
        E.Irreducible ∧
        ∃ (h : Structure.Embedding E P),
          (¬ ∃ k : Structure.Embedding E w.source,
            ∀ x : U,
              Structure.weakImage.quotientMap
                (f := w.toTarget) (k x) = e (h x)) ∧
          ((∃ (g : U → UA),
             E.IsWeakHomomorphism Left g ∧
             (∀ x : U, jL (g x) = (e (h x)).1) ∧
             ((∃ (R : L.RelSymbol) (xs : Fin (L.relArity R) → U),
               Left.rel R (g ∘ xs) ∧ ¬ E.rel R xs) ∨
              (∃ (F0 : L.FuncSymbol)
                  (xs : Fin (L.funcArity F0) → U) (z : UA),
                z ∈ Left.func F0 (g ∘ xs) ∧
                z ∉ imageSet g (E.func F0 xs) ∧
                ∀ ys : Fin (L.funcArity F0) → w.Carrier,
                  (∀ i, w.toTarget (ys i) = (e (h (xs i))).1) →
                  (¬ FunctionInputCoveredByFullIrreducibleTest
                     w.source F0 ys) ∧
                  w.source.func F0 ys = ∅))) ∨
           (∃ (g : U → UB),
             E.IsWeakHomomorphism Right g ∧
             (∀ x : U, jR (g x) = (e (h x)).1) ∧
             ((∃ (R : L.RelSymbol) (xs : Fin (L.relArity R) → U),
               Right.rel R (g ∘ xs) ∧ ¬ E.rel R xs) ∨
              (∃ (F0 : L.FuncSymbol)
                  (xs : Fin (L.funcArity F0) → U) (z : UB),
                z ∈ Right.func F0 (g ∘ xs) ∧
                z ∉ imageSet g (E.func F0 xs) ∧
                ∀ ys : Fin (L.funcArity F0) → w.Carrier,
                  (∀ i, w.toTarget (ys i) = (e (h (xs i))).1) →
                  (¬ FunctionInputCoveredByFullIrreducibleTest
                     w.source F0 ys) ∧
                  w.source.func F0 ys = ∅)))) := by
  obtain ⟨Z, P, hP, e, U, E, hIrr, h, hNoLift, hSide⟩ :=
    badForbiddenWeakImageTest_hasSideReflectionDefect
      F Root Left Right Target sL sR jL jR hFree w hBad
  refine ⟨Z, P, hP, e, U, E, hIrr, h, hNoLift, ?_⟩
  rcases hSide with
      ⟨g, hgWeak, hgCoords, hSurplus⟩ |
      ⟨g, hgWeak, hgCoords, hSurplus⟩
  · left
    refine ⟨g, hgWeak, hgCoords, ?_⟩
    rcases hSurplus with hRelation | hFunction
    · exact Or.inl hRelation
    · obtain ⟨F0, xs, z, hSideValue, hMissing⟩ := hFunction
      refine Or.inr ⟨F0, xs, z, hSideValue, hMissing, ?_⟩
      intro ys hInputCoords
      have hUncovered :=
        weakImageFullTest_sideExtraFunction_forcesUncoveredSourceInput
          w.source Target w.toTarget w.homEmbedding
          E (e.comp h) Left jL g hgCoords
          F0 xs z hSideValue hMissing ys hInputCoords
      exact ⟨hUncovered,
        uncoveredFunctionInput_sourceFibre_empty
          w.source F0 ys hUncovered⟩
  · right
    refine ⟨g, hgWeak, hgCoords, ?_⟩
    rcases hSurplus with hRelation | hFunction
    · exact Or.inl hRelation
    · obtain ⟨F0, xs, z, hSideValue, hMissing⟩ := hFunction
      refine Or.inr ⟨F0, xs, z, hSideValue, hMissing, ?_⟩
      intro ys hInputCoords
      have hUncovered :=
        weakImageFullTest_sideExtraFunction_forcesUncoveredSourceInput
          w.source Target w.toTarget w.homEmbedding
          E (e.comp h) Right jR g hgCoords
          F0 xs z hSideValue hMissing ys hInputCoords
      exact ⟨hUncovered,
        uncoveredFunctionInput_sourceFibre_empty
          w.source F0 ys hUncovered⟩


/-- Genuine free-amalgam corollary for nullary/unary native
functional languages: a bad forbidden full weak-image test
has only an EXTRA RELATION tuple in one full target side.
The function-fibre surplus case is eliminated WITHOUT a
separate global source input-test cover hypothesis.

No claim is made that the remaining relation-surplus
alternative is impossible under maximal common lifts. -/
theorem badForbiddenWeakImageTest_hasExtraRelation_of_unaryFunctions
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hArity : ∀ G : L.FuncSymbol, L.funcArity G ≤ 1)
    {UX UA UB UT : Type}
    (Root : Structure L UX)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (sL : Structure.Embedding Root Left)
    (sR : Structure.Embedding Root Right)
    (jL : Structure.Embedding Left Target)
    (jR : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam sL sR jL jR)
    (w : ForbiddenEHNWitness F Target)
    (hBad : HasForbiddenWeakImageBadIrreducibleTest F Target w) :
    ∃ (Z : Type) (P : Structure L Z),
      F P ∧
      ∃ (e : Structure.Embedding P
        (Structure.weakImage w.source Target w.toTarget))
        (U : Type) (E : Structure L U),
        E.Irreducible ∧
        ∃ (h : Structure.Embedding E P),
          (¬ ∃ k : Structure.Embedding E w.source,
            ∀ x : U,
              Structure.weakImage.quotientMap
                (f := w.toTarget) (k x) = e (h x)) ∧
          ((∃ g : U → UA,
             E.IsWeakHomomorphism Left g ∧
             (∀ x : U, jL (g x) = (e (h x)).1) ∧
             ∃ (R : L.RelSymbol)
               (xs : Fin (L.relArity R) → U),
               Left.rel R (g ∘ xs) ∧ ¬ E.rel R xs) ∨
           (∃ g : U → UB,
             E.IsWeakHomomorphism Right g ∧
             (∀ x : U, jR (g x) = (e (h x)).1) ∧
             ∃ (R : L.RelSymbol)
               (xs : Fin (L.relArity R) → U),
               Right.rel R (g ∘ xs) ∧ ¬ E.rel R xs)) := by
  exact badForbiddenWeakImageTest_hasSideExtraRelation_of_sourceInputTests
    F Root Left Right Target sL sR jL jR hFree
    w (functionInputTuplesCovered_of_allFuncArity_le_one
      w.source hArity) hBad

/-- Positive special case of the printed image-injectivization
step: for a language with NO relation symbols and only nullary
or unary native set-valued function symbols, every source
function-input tuple automatically has a full irreducible
test. Thus there can be no extra native function output in
the full induced image, and there are no relation tuples
requiring coverage. The original tuple-surjective forbidden
image-closure axiom then yields an ACTUAL injective forbidden
EHN witness attaining a global minimum of source support
in any chosen target region.

This is an unconditional language-restricted injectivization
theorem, NOT a proof of the whole 2019 strong-amalgamation
or Ramsey theorem (the geometric flip/Claim 2 is separate). -/
theorem exists_injectiveMinimalForbiddenEHNWitness_of_unaryFunctions_noRelations
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    [IsEmpty L.RelSymbol]
    (hArity : ∀ G : L.FuncSymbol, L.funcArity G ≤ 1)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      ∀ w : ForbiddenEHNWitness F Target,
        v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  have hInputCover :
      ∀ {V : Type} (Src : Structure L V),
        F Src → FunctionInputTuplesCoveredByIrreducibleTests Src := by
    intro V Src _
    exact functionInputTuplesCovered_of_allFuncArity_le_one
      Src hArity
  have hRelationCover :
      ∀ w : ForbiddenEHNWitness F Target,
        SourceRelationTuplesCoveredOnRange
          w.source Target w.toTarget := by
    intro w R
    exact isEmptyElim R
  exact exists_injectiveMinimalForbiddenEHNWitness_of_printedClosure_and_covers
    F hFiniteF hImage hInputCover
    Target AOnly hRelationCover hExists


/-- Positive second special case of the literal printed
image-normalization step. If there are NO native relation
symbols and every member of the forbidden family has
EVERY native set-valued function application defined
(nonempty fibre), at ARBITRARY function arities, then
the family-level printed tuple-surjective image closure
guarantees a globally source-support-minimal INJECTIVE
forbidden EHN witness whenever any forbidden EHN witness
exists in the target.

This is the total-function analogue of the nullary/unary
partial-function theorem above. Neither result establishes
the unrestricted Section 3 strong amalgamation or Claim 2. -/
theorem exists_injectiveMinimalForbiddenEHNWitness_of_totalFunctions_noRelations
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    [IsEmpty L.RelSymbol]
    (hTotal : ∀ {V : Type} (Src : Structure L V),
      F Src →
      ∀ G : L.FuncSymbol,
        ∀ xs : Fin (L.funcArity G) → V,
          (Src.func G xs).Nonempty)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      ∀ w : ForbiddenEHNWitness F Target,
        v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  have hInputCover :
      ∀ {V : Type} (Src : Structure L V),
        F Src → FunctionInputTuplesCoveredByIrreducibleTests Src := by
    intro V Src hSrc
    exact functionInputTuplesCovered_of_allSourceFunctionsDefined
      Src (hTotal Src hSrc)
  have hRelationCover :
      ∀ w : ForbiddenEHNWitness F Target,
        SourceRelationTuplesCoveredOnRange
          w.source Target w.toTarget := by
    intro w R
    exact isEmptyElim R
  exact exists_injectiveMinimalForbiddenEHNWitness_of_printedClosure_and_covers
    F hFiniteF hImage hInputCover
    Target AOnly hRelationCover hExists

end AllThoseRamseyClasses.Lifts
