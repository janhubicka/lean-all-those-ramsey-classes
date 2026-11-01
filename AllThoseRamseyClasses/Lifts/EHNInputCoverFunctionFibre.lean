import AllThoseRamseyClasses.Lifts.EHNPrintedTupleSupportMinimizer
import AllThoseRamseyClasses.Lifts.EHNInputTestCoverageClosedRange
import Mathlib.Tactic

/-!
# Track D: irreducible source function-input tests cover entire target fibres

The existing `ehn_range_isClosed_of_irreducibleInputCover` only
records that every value at an image input remains inside the
source-image range. Its proof actually yields a stronger identity:

  imageSet f (A.func F xs) = B.func F (f ∘ xs)

for EVERY native function symbol and EVERY source input tuple,
whenever all native source function-input tuples occur in a full
irreducible source test and f is an EHN weak homomorphism-embedding.

Consequently the FUNCTION-DOMAIN part of the original 2019
tuple-surjectivity follows on the actual induced range, without
adding any separate assumption about function-domain images.
The only missing tuple-surjectivity premise is now surjectivity on
the OLD positive RELATION tuples of that full induced range.

This does NOT infer relation reflection or relation-tuple
surjectivity from weak EHN. The finite C5/T example shows exactly
why those implications are unavailable.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Genuine exact equality of all native target function fibres
at source image inputs, obtained from full irreducible input
tests; much stronger than range closedness. -/
theorem ehn_fullFunctionFibre_of_inputTests
    {V W : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (hCover : FunctionInputTuplesCoveredByIrreducibleTests A)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V) :
    imageSet f (A.func F xs) = B.func F (f ∘ xs) := by
  classical
  ext out
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hf.1.2 F xs z hz
  · intro hOut
    obtain ⟨U, E, hIrred, e, ys, he⟩ := hCover F xs
    obtain ⟨g, hg⟩ := hf.2 E hIrred e
    have hArgs : g ∘ ys = f ∘ xs := by
      funext i
      calc
        g (ys i) = f (e (ys i)) := hg (ys i)
        _ = f (xs i) := congrArg f (he i)
    have hB : out ∈ B.func F (g ∘ ys) := by
      rw [hArgs]
      exact hOut
    have hG : out ∈ imageSet g (E.func F ys) := by
      rw [g.map_func F ys]
      exact hB
    obtain ⟨z, hz, hgz⟩ := hG
    have hE : e z ∈ imageSet e (E.func F ys) :=
      ⟨z, hz, rfl⟩
    rw [e.map_func F ys] at hE
    have hSourceArgs : e ∘ ys = xs := by
      funext i
      exact he i
    rw [hSourceArgs] at hE
    exact ⟨e z, hE, (hg z).symm.trans hgz⟩

/-- Old relation tuples in the FULL ambient target induced on the
source-image carrier must be represented by actual positive
source relation tuples. This is precisely the part not implied
by weak EHN or by a source function-input test cover. -/
def SourceRelationTuplesCoveredOnRange
    {V W : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W) : Prop :=
  ∀ (R : L.RelSymbol) (zs : Fin (L.relArity R) → W),
    (∀ i, zs i ∈ Set.range f) →
    B.rel R zs →
    ∃ ys : Fin (L.relArity R) → V,
      A.rel R ys ∧ zs = f ∘ ys

/-- Source irreducible function-input test coverage handles ALL
function-domain tuples. If the old RELATION tuples of the actual
full range are also covered, the source-to-induced-range map
is original-partial tuple-surjective, with no extra function
domain premise. The native function-closed range is proved,
not assumed. -/
theorem ehn_actualInducedRange_tupleSurjective_of_inputTests_and_relationCover
    {V W : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (hCover : FunctionInputTuplesCoveredByIrreducibleTests A)
    (hRelations : SourceRelationTuplesCoveredOnRange A B f) :
    OriginalPartialTupleSurjective
      A
      (B.induce (Set.range f)
        (ehn_range_isClosed_of_irreducibleInputCover
          A B f hf hCover))
      (fun x => (⟨f x, ⟨x, rfl⟩⟩ : Set.range f)) := by
  classical
  constructor
  · intro R zs hRel
    let raw : Fin (L.relArity R) → W := Subtype.val ∘ zs
    have hRange : ∀ i, raw i ∈ Set.range f :=
      fun i => (zs i).2
    obtain ⟨ys, hSrc, hEq⟩ :=
      hRelations R raw hRange (show B.rel R raw from hRel)
    refine ⟨ys, hSrc, ?_⟩
    funext i
    exact Subtype.ext (congrFun hEq i)
  · intro F zs hDomain
    choose ys hys using (fun i : Fin (L.funcArity F) => (zs i).2)
    have hArgs : f ∘ ys = Subtype.val ∘ zs := by
      funext i
      exact hys i
    obtain ⟨z, hz⟩ := hDomain
    have hzB : z.1 ∈ B.func F (f ∘ ys) := by
      rw [hArgs]
      exact hz
    have hzImage : z.1 ∈ imageSet f (A.func F ys) := by
      rw [ehn_fullFunctionFibre_of_inputTests
        A B f hf hCover F ys]
      exact hzB
    obtain ⟨y, hy, _⟩ := hzImage
    refine ⟨ys, ⟨y, hy⟩, ?_⟩
    funext i
    exact Subtype.ext (hys i).symm

/-- A positive, fully explicit sufficient condition for the
paper-shaped injective left-support-minimizer step: native source
input-test coverage plus old relation tuple coverage for each
candidate, in addition to the printed image-closure clause.

Neither coverage assumption follows automatically from mere
connectedness/regularity of the forbidden family. The actual
maximal-lift setting may eventually justify the relation coverage
or develop an alternative collision-tolerant argument. -/
theorem exists_injectiveMinimalForbiddenEHNWitness_of_printedClosure_and_covers
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    (hInputCover :
      ∀ {V : Type} (Src : Structure L V),
        F Src → FunctionInputTuplesCoveredByIrreducibleTests Src)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (hRelationCover :
      ∀ w : ForbiddenEHNWitness F Target,
        SourceRelationTuplesCoveredOnRange
          w.source Target w.toTarget)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      ∀ w : ForbiddenEHNWitness F Target,
        v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  have hRanges :
      ∀ w : ForbiddenEHNWitness F Target,
        ∃ hClosed : Target.IsClosed (Set.range w.toTarget),
          OriginalPartialTupleSurjective
            w.source
            (Target.induce (Set.range w.toTarget) hClosed)
            (fun x => (⟨w.toTarget x, ⟨x, rfl⟩⟩ :
              Set.range w.toTarget)) := by
    intro w
    have hCovered := hInputCover w.source w.forbidden
    let hClosed : Target.IsClosed (Set.range w.toTarget) :=
      ehn_range_isClosed_of_irreducibleInputCover
        w.source Target w.toTarget w.homEmbedding hCovered
    refine ⟨hClosed, ?_⟩
    exact ehn_actualInducedRange_tupleSurjective_of_inputTests_and_relationCover
      w.source Target w.toTarget w.homEmbedding hCovered
      (hRelationCover w)
  exact exists_injectiveMinimalForbiddenEHNWitness_of_printedTupleRanges
    F hFiniteF hImage Target AOnly hRanges hExists

end AllThoseRamseyClasses.Lifts
