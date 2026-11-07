import AllThoseRamseyClasses.Lifts.EHNWeakSideFullReflectionDefect
import AllThoseRamseyClasses.Lifts.EHNInputTestCoverageClosedRange
import AllThoseRamseyClasses.Lifts.EHNInputCoverFunctionFibre

/-!
# Track D: extra target relations expose uncovered source input tuples

The source-generated weak quotient Q records exactly the positive
old source incidences. A FULL irreducible substructure E of Q
cannot lack a relation which is supplied by a positive old source
tuple at exactly the same quotient coordinates.

There is a stronger, EHN-specific conclusion. If ANY original
source tuple at those target coordinates lies inside a FULL
irreducible source test, then the original EHN map reflects
the target's positive relation into that source test. The
old source tuple becomes positive, hence generates the tuple
inside Q, contradicting the full E -> Q embedding.

Consequently EVERY source tuple at the coordinates of the
extra side relation is uncovered by full irreducible source
tests. In particular its actual function-closed generated
hull must be reducible and have a proper native FULL free
decomposition. This requires no GLOBAL tuple-coverage
condition or restriction on arities.

This complements the independent local-function analysis.
It is a precise source-geometric obstruction, not a proof
that the original maximal-lift compatibility eliminates it.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An old relation-input tuple is covered if some FULL
irreducible source test contains all of its coordinates.
The test may contain additional vertices; no positivity
of this particular relation tuple is assumed. -/
def RelationInputCoveredByFullIrreducibleTest
    {V : Type} (A : Structure L V)
    (R : L.RelSymbol)
    (xs : Fin (L.relArity R) → V) : Prop :=
  ∃ (U : Type) (E : Structure L U),
    E.Irreducible ∧
    ∃ (e : Structure.Embedding E A)
      (ys : Fin (L.relArity R) → U),
      ∀ i, e (ys i) = xs i

/-- A source tuple protected by ONE full irreducible
source test reflects any positive target relation at
its image coordinates, by the original EHN clause.

There is no global relation tuple-surjectivity assumption. -/
theorem ehn_localRelationInputCover_reflectsTargetPositive
    {V W : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (R : L.RelSymbol)
    (xs : Fin (L.relArity R) → V)
    (hCovered : RelationInputCoveredByFullIrreducibleTest A R xs)
    (hTarget : B.rel R (f ∘ xs)) :
    A.rel R xs := by
  obtain ⟨U, E, hIrred, e, ys, he⟩ := hCovered
  obtain ⟨g, hg⟩ := hf.2 E hIrred e
  have hArgs : g ∘ ys = f ∘ xs := by
    funext i
    calc
      g (ys i) = f (e (ys i)) := hg (ys i)
      _ = f (xs i) := congrArg f (he i)
  have hImage : B.rel R (g ∘ ys) := by
    rw [hArgs]
    exact hTarget
  have hE : E.rel R ys := (g.map_rel_iff R ys).mp hImage
  have hA : A.rel R (e ∘ ys) :=
    (e.map_rel_iff R ys).mpr hE
  have hSourceArgs : e ∘ ys = xs := by
    funext i
    exact he i
  rw [hSourceArgs] at hA
  exact hA

/-- The extra positive relation of a side-local FULL quotient
test forces EVERY original source tuple at those precise
quotient coordinates to be uncovered by full irreducible
source tests. This holds even if the old EHN map collapses
other, unrelated source vertices. -/
theorem weakImageFullTest_sideExtraRelation_forcesUncoveredSourceInput
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
    (hMissing : ¬ E.rel R xs)
    (ys : Fin (L.relArity R) → V)
    (hInputCoords : ∀ i, f (ys i) = (e (xs i)).1) :
    ¬ RelationInputCoveredByFullIrreducibleTest A R ys := by
  intro hCovered
  have hB : B.rel R (j ∘ (g ∘ xs)) :=
    (j.map_rel_iff R (g ∘ xs)).mpr hSide
  have hArgs : f ∘ ys = j ∘ (g ∘ xs) := by
    funext i
    calc
      f (ys i) = (e (xs i)).1 := hInputCoords i
      _ = j (g (xs i)) := (hCoords (xs i)).symm
  have hTarget : B.rel R (f ∘ ys) := by
    rw [hArgs]
    exact hB
  have hSource : A.rel R ys :=
    ehn_localRelationInputCover_reflectsTargetPositive
      A B f hf R ys hCovered hTarget
  have hQuotient :
      (Structure.weakImage A B f).rel R (e ∘ xs) := by
    change ∃ (args : Fin (L.relArity R) → V),
      A.rel R args ∧
      ∀ i, (e ∘ xs) i =
        (⟨f (args i), ⟨args i, rfl⟩⟩ : Set.range f)
    exact ⟨ys, hSource, fun i => Subtype.ext (hInputCoords i).symm⟩
  exact hMissing ((e.map_rel_iff R xs).mp hQuotient)

/-- An uncovered old relation-input tuple has a REDUCIBLE
native function-closed generated hull: if this full hull
were irreducible, its full inclusion into the source would
itself protect the tuple. -/
theorem uncoveredRelationInput_generatedHull_notIrreducible
    {V : Type} (A : Structure L V)
    (R : L.RelSymbol)
    (ys : Fin (L.relArity R) → V)
    (hUncovered :
      ¬ RelationInputCoveredByFullIrreducibleTest A R ys) :
    ¬ (A.induce (A.functionClosure (Set.range ys))
       (A.functionClosure_isClosed (Set.range ys))).Irreducible := by
  intro hIrred
  let S : Set V := A.functionClosure (Set.range ys)
  have hS : A.IsClosed S :=
    A.functionClosure_isClosed (Set.range ys)
  let E : Structure L S := A.induce S hS
  let inc : Structure.Embedding E A := A.inclusion S hS
  let inputs : Fin (L.relArity R) → S :=
    fun i => ⟨ys i,
      A.subset_functionClosure (Set.range ys) ⟨i, rfl⟩⟩
  apply hUncovered
  exact ⟨S, E, hIrred, inc, inputs, fun _ => rfl⟩

/-- Every uncovered relation-input tuple has an ACTUAL
proper native FULL free decomposition of its input-generated
function-closed hull, not just graph-theoretic nonadjacency. -/
theorem uncoveredRelationInput_generatedHull_decomposes
    {V : Type} (A : Structure L V)
    (R : L.RelSymbol)
    (ys : Fin (L.relArity R) → V)
    (hUncovered :
      ¬ RelationInputCoveredByFullIrreducibleTest A R ys) :
    Nonempty (ProperFreeDecomposition
      (A.induce (A.functionClosure (Set.range ys))
        (A.functionClosure_isClosed (Set.range ys)))) := by
  have hNotIrred :=
    uncoveredRelationInput_generatedHull_notIrreducible
      A R ys hUncovered
  by_contra hNoDecomposition
  exact hNotIrred
    ((irreducible_iff_noProperFreeDecomposition
      (A.induce (A.functionClosure (Set.range ys))
        (A.functionClosure_isClosed (Set.range ys)))).mpr
       hNoDecomposition)

/-- A side-only extra relation of a FULL quotient test
forces a proper native free decomposition of the generated
hull of EVERY original source tuple at the prescribed
coordinates. No global relation- or function-input coverage. -/
theorem weakImageFullTest_sideExtraRelation_forcesSourceInputDecomposition
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
    (hMissing : ¬ E.rel R xs)
    (ys : Fin (L.relArity R) → V)
    (hInputCoords : ∀ i, f (ys i) = (e (xs i)).1) :
    Nonempty (ProperFreeDecomposition
      (A.induce (A.functionClosure (Set.range ys))
        (A.functionClosure_isClosed (Set.range ys)))) := by
  exact uncoveredRelationInput_generatedHull_decomposes A R ys
    (weakImageFullTest_sideExtraRelation_forcesUncoveredSourceInput
      A B f hf E e Side j g hCoords R xs
      hSide hMissing ys hInputCoords)


/-- ALL old relation-input tuples in a source are covered
by full irreducible source tests. This hypothesis concerns
all tuples, including those where the relation is FALSE;
it is not implied by mere connectedness of the source.

This is the precise relation-side analogue of
`FunctionInputTuplesCoveredByIrreducibleTests`. -/
def RelationInputTuplesCoveredByIrreducibleTests
    {V : Type} (A : Structure L V) : Prop :=
  ∀ (R : L.RelSymbol) (xs : Fin (L.relArity R) → V),
    RelationInputCoveredByFullIrreducibleTest A R xs

/-- Full irreducible source-test coverage for each OLD
relation-input tuple implies relation-tuple surjectivity
onto the actual full target image under an EHN map.

Target relation tuples whose coordinates lie in the image
are reflected at any chosen preimage input tuple, and so
have a positive original-source witness. -/
theorem ehn_sourceRelationTuplesCoveredOnRange_of_inputTests
    {V W : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (hCover : RelationInputTuplesCoveredByIrreducibleTests A) :
    SourceRelationTuplesCoveredOnRange A B f := by
  classical
  intro R zs hRange hTarget
  let xs : Fin (L.relArity R) → V :=
    fun i => Classical.choose (hRange i)
  have hArgs : zs = f ∘ xs := by
    funext i
    exact (Classical.choose_spec (hRange i)).symm
  have hPositive : A.rel R xs := by
    apply ehn_localRelationInputCover_reflectsTargetPositive
      A B f hf R xs (hCover R xs)
    rw [← hArgs]
    exact hTarget
  exact ⟨xs, hPositive, hArgs⟩

/-- A clean CONDITIONAL positive injectivization theorem
in the exact printed 2019 tuple-image semantics:
if every forbidden source has FULL irreducible input-test
coverage for BOTH its native function and relation symbols,
then source-support minimum forbidden EHN witnesses can
be made injective, even with arbitrary native arities.

The two cover hypotheses are explicit. Neither follows
from connectedness/regularity of the forbidden family. -/
theorem exists_injectiveMinimalForbiddenEHNWitness_of_bothInputCovers
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    (hFunctionInputCover :
      ∀ {V : Type} (Src : Structure L V),
        F Src → FunctionInputTuplesCoveredByIrreducibleTests Src)
    (hRelationInputCover :
      ∀ {V : Type} (Src : Structure L V),
        F Src → RelationInputTuplesCoveredByIrreducibleTests Src)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      ∀ w : ForbiddenEHNWitness F Target,
        v.sourceSupportCount AOnly ≤
          w.sourceSupportCount AOnly := by
  have hRelationCover :
      ∀ w : ForbiddenEHNWitness F Target,
        SourceRelationTuplesCoveredOnRange
          w.source Target w.toTarget := by
    intro w
    exact ehn_sourceRelationTuplesCoveredOnRange_of_inputTests
      w.source Target w.toTarget w.homEmbedding
      (hRelationInputCover w.source w.forbidden)
  exact exists_injectiveMinimalForbiddenEHNWitness_of_printedClosure_and_covers
    F hFiniteF hImage hFunctionInputCover
    Target AOnly hRelationCover hExists

end AllThoseRamseyClasses.Lifts
