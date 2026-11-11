import AllThoseRamseyClasses.Lifts.EHNWeakImageUncoveredRelationInput
import AllThoseRamseyClasses.Lifts.EHNWeakImageUncoveredFunctionInput

/-!
# Track D: actual crossing source representatives of weak-image side defects

The previously checked local theorems quantify over every original source tuple
at the quotient coordinates of a side surplus. This module supplies the missing
EXISTENTIAL witness: each quotient coordinate is literally a member of the
source map's range, so all finitely many coordinates have simultaneous actual
source representatives, even when the source map has root collisions.

For either a relation surplus or a function-fibre surplus, the representatives
generate an ACTUAL reducible function-closed source hull and cross both sides
of an ACTUAL proper full native free decomposition. In the function case the
original source operation is also UNDEFINED at these chosen inputs.

These are concrete local certificates, NOT a proof that maximal common-lift
profiles exclude the certificates, and NOT unrestricted image injectivization.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A target-side extra relation on a full weak-quotient test has an ACTUAL
matching original source input tuple. Its function-closed source hull has a
proper full native free decomposition, with generators crossing both sides.

This removes the possible vacuity of a universally quantified
"every matching original tuple" formulation. The source map need not
be injective at any unrelated vertex or geometric root. -/
theorem weakImageFullTest_sideExtraRelation_exhibitsCrossingSourceTuple
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
    (R : L.RelSymbol)
    (xs : Fin (L.relArity R) → U)
    (hSide : Side.rel R (g ∘ xs))
    (hMissing : ¬ E.rel R xs) :
    ∃ ys : Fin (L.relArity R) → V,
      (∀ i, f (ys i) = (e (xs i)).1) ∧
      (¬ RelationInputCoveredByFullIrreducibleTest A R ys) ∧
      ∃ d : ProperFreeDecomposition
          (A.induce (A.functionClosure (Set.range ys))
            (A.functionClosure_isClosed (Set.range ys))),
        (¬ ∀ i : Fin (L.relArity R), ∃ a : d.Left,
          Structure.closureLift A ys i = d.leftIn a) ∧
        (¬ ∀ i : Fin (L.relArity R), ∃ b : d.Right,
          Structure.closureLift A ys i = d.rightIn b) := by
  classical
  let ys : Fin (L.relArity R) → V :=
    fun i => Classical.choose ((e (xs i)).property)
  have hRep : ∀ i, f (ys i) = (e (xs i)).1 := by
    intro i
    exact Classical.choose_spec ((e (xs i)).property)
  have hUncovered : ¬ RelationInputCoveredByFullIrreducibleTest A R ys :=
    weakImageFullTest_sideExtraRelation_forcesUncoveredSourceInput
      A B f hf E e Side j g hCoords R xs hSide hMissing ys hRep
  exact ⟨ys, hRep, hUncovered,
    uncoveredRelationInput_hasCrossingFreeDecomposition A R ys hUncovered⟩

/-- A target-side extra function value on a full weak-quotient test has an
ACTUAL matching original source input tuple whose original operation fibre
is EMPTY. Its generated closed hull admits a genuine proper native free
decomposition crossed by all input generators collectively.

In particular this defect is not only a weak-image test mismatch: it is
witnessed by actual uncovered, undefined, reducibly generated source inputs. -/
theorem weakImageFullTest_sideExtraFunction_exhibitsCrossingUndefinedSourceTuple
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
    ∃ ys : Fin (L.funcArity F) → V,
      (∀ i, f (ys i) = (e (xs i)).1) ∧
      (¬ FunctionInputCoveredByFullIrreducibleTest A F ys) ∧
      A.func F ys = ∅ ∧
      ∃ d : ProperFreeDecomposition
          (A.induce (A.functionClosure (Set.range ys))
            (A.functionClosure_isClosed (Set.range ys))),
        (¬ ∀ i : Fin (L.funcArity F), ∃ a : d.Left,
          Structure.closureLift A ys i = d.leftIn a) ∧
        (¬ ∀ i : Fin (L.funcArity F), ∃ b : d.Right,
          Structure.closureLift A ys i = d.rightIn b) := by
  classical
  let ys : Fin (L.funcArity F) → V :=
    fun i => Classical.choose ((e (xs i)).property)
  have hRep : ∀ i, f (ys i) = (e (xs i)).1 := by
    intro i
    exact Classical.choose_spec ((e (xs i)).property)
  have hUncovered : ¬ FunctionInputCoveredByFullIrreducibleTest A F ys :=
    weakImageFullTest_sideExtraFunction_forcesUncoveredSourceInput
      A B f hf E e Side j g hCoords
      F xs z hSideValue hMissing ys hRep
  have hEmpty : A.func F ys = ∅ :=
    uncoveredFunctionInput_sourceFibre_empty A F ys hUncovered
  obtain ⟨d⟩ :=
    uncoveredFunctionInput_generatedClosedHull_decomposes A F ys hUncovered
  exact ⟨ys, hRep, hUncovered, hEmpty, d,
    generatedClosedHull_properFreeDecomposition_inputsCross A ys d⟩


/-- An EHN map cannot identify two DISTINCT elements of any
irreducible full source test. Consequently, if it collapses two
actual members of a generating tuple, that tuple's genuine
function-closed generated hull has a proper full native free
decomposition. No finite carrier, source test-cover condition,
target free amalgam or root-width assumption is needed. -/
theorem ehn_generatorCollision_forcesSourceHullDecomposition
    {V W X : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (xs : X → V)
    (i j : X)
    (hDistinct : xs i ≠ xs j)
    (hCollision : f (xs i) = f (xs j)) :
    Nonempty (ProperFreeDecomposition
      (A.induce (A.functionClosure (Set.range xs))
        (A.functionClosure_isClosed (Set.range xs)))) := by
  have hNotIrred :
      ¬ (A.induce (A.functionClosure (Set.range xs))
          (A.functionClosure_isClosed (Set.range xs))).Irreducible := by
    intro hIrred
    let S : Set V := A.functionClosure (Set.range xs)
    have hS : A.IsClosed S :=
      A.functionClosure_isClosed (Set.range xs)
    let E : Structure L S := A.induce S hS
    let inc : Structure.Embedding E A := A.inclusion S hS
    obtain ⟨g, hg⟩ := hf.2 E hIrred inc
    let a : S := ⟨xs i,
      A.subset_functionClosure (Set.range xs) ⟨i, rfl⟩⟩
    let b : S := ⟨xs j,
      A.subset_functionClosure (Set.range xs) ⟨j, rfl⟩⟩
    have hab : g a = g b := by
      calc
        g a = f (inc a) := hg a
        _ = f (xs i) := rfl
        _ = f (xs j) := hCollision
        _ = f (inc b) := rfl
        _ = g b := (hg b).symm
    exact hDistinct (congrArg Subtype.val (g.injective hab))
  by_contra hNoDecomposition
  exact hNotIrred
    ((irreducible_iff_noProperFreeDecomposition
      (A.induce (A.functionClosure (Set.range xs))
        (A.functionClosure_isClosed (Set.range xs)))).mpr
      hNoDecomposition)

/-- A source collision on two generators thus produces an ACTUAL
proper full native free decomposition of their generated hull
whose two proper sides EACH miss at least one generator.

This links the root-collision alternative of the Section 3
minimal-obstruction dichotomy to the same crossing source
geometry as the relation/function surplus alternatives.
It does not exclude any of these configurations. -/
theorem ehn_generatorCollision_exhibitsCrossingSourceHull
    {V W X : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (xs : X → V)
    (i j : X)
    (hDistinct : xs i ≠ xs j)
    (hCollision : f (xs i) = f (xs j)) :
    ∃ d : ProperFreeDecomposition
        (A.induce (A.functionClosure (Set.range xs))
          (A.functionClosure_isClosed (Set.range xs))),
      (¬ ∀ k : X, ∃ a : d.Left,
        Structure.closureLift A xs k = d.leftIn a) ∧
      (¬ ∀ k : X, ∃ b : d.Right,
        Structure.closureLift A xs k = d.rightIn b) := by
  obtain ⟨d⟩ :=
    ehn_generatorCollision_forcesSourceHullDecomposition
      A B f hf xs i j hDistinct hCollision
  exact ⟨d,
    generatedClosedHull_properFreeDecomposition_inputsCross A xs d⟩


end AllThoseRamseyClasses.Lifts
