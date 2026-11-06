import AllThoseRamseyClasses.Lifts.EHNWeakSideFullReflectionDefect
import AllThoseRamseyClasses.Lifts.EHNInputCoverFunctionFibre
import Mathlib.Data.Fintype.Card

/-!
# Track D: source irreducible function-input tests eliminate weak-image fibre defects

The existing `ehn_fullFunctionFibre_of_inputTests` theorem proves
that an EHN forbidden-source map preserves all target native
function-value fibres, not just closedness of the vertex image,
if every source function-input tuple belongs to a FULL
irreducible source test.

The SOURCE-GENERATED weak image Q is incidence-generated: each
Q-function value arises from a source function incidence under
some input preimages. Therefore the previous full-fibre equality
implies Q's weak inclusion into Target is EXACTLY surjective
on every target function fibre at Q-inputs.

For every FULL irreducible test E embedded in Q, the prescribed
map E -> Target thus also preserves COMPLETE function fibres,
even though it may fail relation reflection. The same is true
for a weak factorization E -> Side through any FULL embedded
target side. Consequently the bad-test alternative from the
original Track D support-minimizer dichotomy can contain ONLY
an extra target RELATION tuple, under the explicit source
input-test coverage hypothesis.

This is not a proof that input-test coverage follows from the
printed regularity/connectedness hypotheses, nor that the
remaining target-only relations are ruled out by maximality.
The verified C5/T counterexample is purely relational and
still witnesses that residual obstruction.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under a SOURCE-side cover by full irreducible native
function-input tests, the inclusion of the source-generated
weak quotient into the ambient target preserves EXACTLY the
entire target function-value fibre at every quotient tuple.

No extra closed-range, vertex injectivity, or relation
tuple-surjectivity condition is assumed. -/
theorem weakImage_inclusion_fullFunctionFibres_of_sourceInputTests
    {V W : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (hCover : FunctionInputTuplesCoveredByIrreducibleTests A)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → Set.range f) :
    imageSet Subtype.val
        ((Structure.weakImage A B f).func F xs) =
      B.func F (Subtype.val ∘ xs) := by
  classical
  ext z
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (Structure.weakImage.inclusion_weak hf.1).2 F xs q hq
  · intro hz
    choose ys hys using (fun i : Fin (L.funcArity F) => (xs i).2)
    have hArgs : f ∘ ys = Subtype.val ∘ xs := by
      funext i
      exact hys i
    have hzB : z ∈ B.func F (f ∘ ys) := by
      rw [hArgs]
      exact hz
    have hzImage : z ∈ imageSet f (A.func F ys) := by
      rw [ehn_fullFunctionFibre_of_inputTests
        A B f hf hCover F ys]
      exact hzB
    obtain ⟨v, hv, hvz⟩ := hzImage
    let qv : Set.range f := ⟨f v, ⟨v, rfl⟩⟩
    have hqv : qv ∈ (Structure.weakImage A B f).func F xs := by
      change ∃ (args : Fin (L.funcArity F) → V) (out : V),
        out ∈ A.func F args ∧
        (∀ i, xs i = ⟨f (args i), ⟨args i, rfl⟩⟩) ∧
        qv = ⟨f out, ⟨out, rfl⟩⟩
      refine ⟨ys, v, hv, ?_, rfl⟩
      intro i
      exact Subtype.ext (hys i).symm
    exact ⟨qv, hqv, hvz⟩

/-- Every FULL substructure E of the source-generated quotient
has an EXACT image of its native function-value fibre in the
original target, provided source input tests are covered.

In particular this is true of the irreducible full tests
inside forbidden full quotient-copies. -/
theorem weakImageFullCopy_fullTargetFunctionFibres_of_sourceInputTests
    {V W U : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (hCover : FunctionInputTuplesCoveredByIrreducibleTests A)
    (E : Structure L U)
    (e : Structure.Embedding E (Structure.weakImage A B f))
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → U) :
    imageSet (fun x : U => (e x).1) (E.func F xs) =
      B.func F ((fun x : U => (e x).1) ∘ xs) := by
  classical
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hq : e v ∈ (Structure.weakImage A B f).func F (e ∘ xs) := by
      rw [← e.map_func F xs]
      exact ⟨v, hv, rfl⟩
    exact (Structure.weakImage.inclusion_weak hf.1).2
      F (e ∘ xs) (e v) hq
  · intro hz
    change z ∈ B.func F (Subtype.val ∘ (e ∘ xs)) at hz
    have hqz :
        z ∈ imageSet Subtype.val
          ((Structure.weakImage A B f).func F (e ∘ xs)) := by
      rw [weakImage_inclusion_fullFunctionFibres_of_sourceInputTests
        A B f hf hCover F (e ∘ xs)]
      exact hz
    obtain ⟨q, hq, hqzEq⟩ := hqz
    have heq : q ∈ imageSet e (E.func F xs) := by
      rw [e.map_func F xs]
      exact hq
    obtain ⟨v, hv, hve⟩ := heq
    exact ⟨v, hv, (congrArg Subtype.val hve).trans hqzEq⟩

/-- A full target-side embedding together with prescribed
coordinate agreement transfers the quotient-derived exact
function-fibre equality into the actual SIDE.

No full or EHN property of the side map is assumed. -/
theorem weakImageFullCopy_side_noExtraFunctionFibres_of_sourceInputTests
    {V W U US : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (hCover : FunctionInputTuplesCoveredByIrreducibleTests A)
    (E : Structure L U)
    (e : Structure.Embedding E (Structure.weakImage A B f))
    (Side : Structure L US)
    (j : Structure.Embedding Side B)
    (g : U → US)
    (hCoords : ∀ x : U, j (g x) = (e x).1) :
    ¬ ∃ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → U)
        (z : US),
      z ∈ Side.func F (g ∘ xs) ∧
        z ∉ imageSet g (E.func F xs) := by
  rintro ⟨F, xs, z, hz, hMissing⟩
  have hB : j z ∈ B.func F (j ∘ (g ∘ xs)) := by
    have hImg : j z ∈ imageSet j (Side.func F (g ∘ xs)) :=
      ⟨z, hz, rfl⟩
    rw [j.map_func F (g ∘ xs)] at hImg
    exact hImg
  have hArgs :
      (fun x : U => (e x).1) ∘ xs =
        j ∘ (g ∘ xs) := by
    funext i
    exact (hCoords (xs i)).symm
  have hTarget :
      j z ∈ B.func F ((fun x : U => (e x).1) ∘ xs) := by
    rw [hArgs]
    exact hB
  have hImage :
      j z ∈ imageSet (fun x : U => (e x).1) (E.func F xs) := by
    rw [weakImageFullCopy_fullTargetFunctionFibres_of_sourceInputTests
      A B f hf hCover E e F xs]
    exact hTarget
  obtain ⟨v, hv, hvz⟩ := hImage
  have hgz : g v = z := by
    apply j.injective
    calc
      j (g v) = (e v).1 := hCoords v
      _ = j z := hvz
  exact hMissing ⟨v, hv, hgz⟩

/-- Full bad-test and side data, but only the RELATION-surplus
alternative survives when the original forbidden source has
full irreducible tests covering all function-input tuples.

The old source-to-target EHN map may still identify vertices.
The chosen irreducible quotient test itself has injective target
images by the previously verified trichotomy theorem. -/
theorem badForbiddenWeakImageTest_hasSideExtraRelation_of_sourceInputTests
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
    (hCover : FunctionInputTuplesCoveredByIrreducibleTests w.source)
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
             (∃ (R : L.RelSymbol) (xs : Fin (L.relArity R) → U),
               Left.rel R (g ∘ xs) ∧ ¬ E.rel R xs)) ∨
           (∃ g : U → UB,
             E.IsWeakHomomorphism Right g ∧
             (∀ x : U, jR (g x) = (e (h x)).1) ∧
             (∃ (R : L.RelSymbol) (xs : Fin (L.relArity R) → U),
               Right.rel R (g ∘ xs) ∧ ¬ E.rel R xs))) := by
  obtain ⟨Z, P, hP, e, U, E, hIrr, h, hNoLift, hSide⟩ :=
    badForbiddenWeakImageTest_hasSideReflectionDefect
      F Root Left Right Target sL sR jL jR hFree w hBad
  refine ⟨Z, P, hP, e, U, E, hIrr, h, hNoLift, ?_⟩
  rcases hSide with
      ⟨g, hgWeak, hgCoords, hSurplus⟩ |
      ⟨g, hgWeak, hgCoords, hSurplus⟩
  · rcases hSurplus with hRelation | hFunction
    · exact Or.inl ⟨g, hgWeak, hgCoords, hRelation⟩
    · have hNoFunction :=
        weakImageFullCopy_side_noExtraFunctionFibres_of_sourceInputTests
          w.source Target w.toTarget w.homEmbedding hCover
          E (e.comp h) Left jL g hgCoords
      exact False.elim (hNoFunction hFunction)
  · rcases hSurplus with hRelation | hFunction
    · exact Or.inr ⟨g, hgWeak, hgCoords, hRelation⟩
    · have hNoFunction :=
        weakImageFullCopy_side_noExtraFunctionFibres_of_sourceInputTests
          w.source Target w.toTarget w.homEmbedding hCover
          E (e.comp h) Right jR g hgCoords
      exact False.elim (hNoFunction hFunction)

end AllThoseRamseyClasses.Lifts
