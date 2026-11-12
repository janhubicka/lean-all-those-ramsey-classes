import AllThoseRamseyClasses.Lifts.EHNInputCoverFunctionFibre
import AllThoseRamseyClasses.Lifts.EHNWeakImageUncoveredFunctionInput
import AllThoseRamseyClasses.Lifts.EHNWeakImageUncoveredRelationInput
import AllThoseRamseyClasses.Lifts.GlobalMinimalMixedPieceFromRootInjOn

/-!
# Track D: exact target-incidence defects of one minimal forbidden witness

The printed tuple-surjective forbidden-image closure controls a
function-closed, tuple-surjective ACTUAL induced target range. A weak
EHN source-to-target map need not satisfy either condition.

Rather than infer source irreducible-test coverage for all input tuples,
look directly at the ACTUAL positive target function fibres at image
arguments, and at positive target OLD relation tuples on image
coordinates. If ALL such incidences lift to original positive source
incidences, the full induced image is function-closed and
original-partial tuple-surjective. The printed closure gives a
source-support-minimal injective forbidden witness. The verified
original full-free-amalgam theorem then chooses its smallest genuine
mixed geometric piece.

Otherwise one can exhibit an ACTUAL target-only positive relation
or function incidence, with actual original source arguments, whose
true native input-generated source hull admits a proper FULL free
decomposition crossed by the input generators. No vacuous
"unprotected input with no target surplus" alternative is needed.

The original unrestricted strong AP and the selected-Q Claim 2
descent remain unproved. In particular no maximal-lift compatibility
principle excluding the target-only incidences is assumed here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every ACTUAL positive target function incidence whose INPUT
coordinates are in the source image has a positive original
source function incidence lifting both those coordinates and
the target output. Source preimages may be chosen freely;
this is a statement about ALL weak-image quotient coordinates,
not only one particular representative source input.

It is an explicit sufficient positive-incidence coverage
condition, not an assertion derived from weak EHN or from the
printed forbidden-image closure. -/
def SourceFunctionValueTuplesCoveredOnRange
    {V W : Type} (A : Structure L V) (B : Structure L W)
    (f : V → W) : Prop :=
  ∀ (G : L.FuncSymbol) (zs : Fin (L.funcArity G) → W)
    (z : W), (∀ i, zs i ∈ Set.range f) →
      z ∈ B.func G zs →
      ∃ (xs : Fin (L.funcArity G) → V) (out : V),
        out ∈ A.func G xs ∧ zs = f ∘ xs ∧ z = f out

/-- Complete positive target function-incidence coverage over
the ACTUAL source-image range makes that range function-closed.
No source irreducible-test cover and no injectivity is used. -/
theorem sourceFunctionValueTuplesCovered_rangeClosed
    {V W : Type} (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hFibre : SourceFunctionValueTuplesCoveredOnRange A B f) :
    B.IsClosed (Set.range f) := by
  intro G zs hzs z hz
  obtain ⟨xs, out, hPositive, hCoords, hValue⟩ :=
    hFibre G zs z hzs hz
  exact ⟨out, hValue.symm⟩

/-- Coverage of all ACTUAL target function values at source-IMAGE
input coordinates, plus positive old-relation incidence coverage
on that SAME image, implies ORIGINAL-PARTIAL tuple-surjectivity
contract for the genuine full induced target range.

This includes the entire native domain/value fibre, not merely
the old relational shadow, and the range is closed by the
preceding theorem rather than by a new assumption. -/
theorem sourceFullIncidenceReflection_inducedRangeTupleSurjective
    {V W : Type} (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hFibre : SourceFunctionValueTuplesCoveredOnRange A B f)
    (hRelation : SourceRelationTuplesCoveredOnRange A B f) :
    OriginalPartialTupleSurjective
      A
      (B.induce (Set.range f)
        (sourceFunctionValueTuplesCovered_rangeClosed A B f hFibre))
      (fun x => (⟨f x, ⟨x, rfl⟩⟩ : Set.range f)) := by
  classical
  constructor
  · intro R zs hRel
    let raw : Fin (L.relArity R) → W := Subtype.val ∘ zs
    have hRange : ∀ i, raw i ∈ Set.range f :=
      fun i => (zs i).2
    obtain ⟨ys, hSource, hEq⟩ :=
      hRelation R raw hRange (show B.rel R raw from hRel)
    refine ⟨ys, hSource, ?_⟩
    funext i
    exact Subtype.ext (congrFun hEq i)
  · intro G zs hDomain
    let raw : Fin (L.funcArity G) → W := Subtype.val ∘ zs
    have hRange : ∀ i, raw i ∈ Set.range f :=
      fun i => (zs i).2
    obtain ⟨z, hz⟩ := hDomain
    have hzB : z.1 ∈ B.func G raw := hz
    obtain ⟨ys, y, hy, hEq, _⟩ :=
      hFibre G raw z.1 hRange hzB
    refine ⟨ys, ⟨y, hy⟩, ?_⟩
    funext i
    exact Subtype.ext (congrFun hEq i)

/-- In the ACTUAL full native free amalgam of two
forbidden-free sides with matching ORIGINAL global canonical
lifts, every nonempty forbidden weak EHN obstruction has
a support-minimal source witness w and ONE of three exact
source-matched alternatives:

1. an ACTUAL additional target function value at original
   source input coordinates, not among positive source
   output images, with a crossing FULL free source hull;
2. an ACTUAL additional positive target relation on original
   source input coordinates, not positive in the source,
   with a crossing FULL free source hull;
3. an INJECTIVE source-support-minimal forbidden witness
   and its smallest genuine mixed geometric piece.

Unlike the broader uncovered-input alternative, a case (1)
certificate is an ACTUAL target-only positive function value.
Both defect alternatives may still occur in a compatible
maximal-lift free amalgam; excluding or resolving them
remains the missing original Section 3 argument. -/
theorem exists_minimalForbiddenWitness_targetIncidenceDefect_or_mixedPiece
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hAvoidLeft : AvoidsGlobalFunctionalEHN F Left)
    (hAvoidRight : AvoidsGlobalFunctionalEHN F Right)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ (w : ForbiddenEHNWitness F Target),
      (∀ t : ForbiddenEHNWitness F Target,
        w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
          t.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
      ((∃ (G : L.FuncSymbol)
            (xs : Fin (L.funcArity G) → w.Carrier) (z : UT),
          z ∈ Target.func G (w.toTarget ∘ xs) ∧
          (¬ ∃ (ys : Fin (L.funcArity G) → w.Carrier)
                (out : w.Carrier),
            out ∈ w.source.func G ys ∧
            w.toTarget ∘ ys = w.toTarget ∘ xs ∧
            w.toTarget out = z) ∧
          ∃ d : ProperFreeDecomposition
              (w.source.induce (w.source.functionClosure (Set.range xs))
                (w.source.functionClosure_isClosed (Set.range xs))),
            (¬ ∀ i : Fin (L.funcArity G), ∃ a : d.Left,
              Structure.closureLift w.source xs i = d.leftIn a) ∧
            (¬ ∀ i : Fin (L.funcArity G), ∃ c : d.Right,
              Structure.closureLift w.source xs i = d.rightIn c)) ∨
       (∃ (R : L.RelSymbol)
            (xs : Fin (L.relArity R) → w.Carrier),
          Target.rel R (w.toTarget ∘ xs) ∧
          ¬ w.source.rel R xs ∧
          ∃ d : ProperFreeDecomposition
              (w.source.induce (w.source.functionClosure (Set.range xs))
                (w.source.functionClosure_isClosed (Set.range xs))),
            (¬ ∀ i : Fin (L.relArity R), ∃ a : d.Left,
              Structure.closureLift w.source xs i = d.leftIn a) ∧
            (¬ ∀ i : Fin (L.relArity R), ∃ c : d.Right,
              Structure.closureLift w.source xs i = d.rightIn c)) ∨
       (∃ (v : ForbiddenEHNWitness F Target),
          Function.Injective v.toTarget ∧
          (∀ t : ForbiddenEHNWitness F Target,
            v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
              t.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
          ∃ P : MixedGeometricPiece v.source
              (weakFreeRootPart (sL := iLeft) (iL := jLeft) v.toTarget)
              (weakFreeLeftPart (sL := iLeft) (iL := jLeft) v.toTarget)
              (weakFreeRightPart
                (sL := iLeft) (iL := jLeft) (iR := jRight) v.toTarget),
            ∀ Q : MixedGeometricPiece v.source
              (weakFreeRootPart (sL := iLeft) (iL := jLeft) v.toTarget)
              (weakFreeLeftPart (sL := iLeft) (iL := jLeft) v.toTarget)
              (weakFreeRightPart
                (sL := iLeft) (iL := jLeft) (iR := jRight) v.toTarget),
              P.nonrootCount ≤ Q.nonrootCount)) := by
  classical
  obtain ⟨w, hMin⟩ :=
    exists_minimalForbiddenEHNWitness_support F Target
      (fullFreeLeftExclusiveTarget iLeft jLeft) hExists
  by_cases hFunction : SourceFunctionValueTuplesCoveredOnRange
      w.source Target w.toTarget
  · by_cases hRelations :
        SourceRelationTuplesCoveredOnRange w.source Target w.toTarget
    · let hClosed : Target.IsClosed (Set.range w.toTarget) :=
        sourceFunctionValueTuplesCovered_rangeClosed
          w.source Target w.toTarget hFunction
      have hTuple : OriginalPartialTupleSurjective
          w.source (Target.induce (Set.range w.toTarget) hClosed)
          (fun x => (⟨w.toTarget x, ⟨x, rfl⟩⟩ :
            Set.range w.toTarget)) :=
        sourceFullIncidenceReflection_inducedRangeTupleSurjective
          w.source Target w.toTarget hFunction hRelations
      obtain ⟨v, hInjective, hBound⟩ :=
        forbiddenEHNWitness_injectiveReplacement_of_printedTupleRange
          F hFiniteF hImage Target
          (fullFreeLeftExclusiveTarget iLeft jLeft)
          w hClosed hTuple
      have hMinimalV : ∀ t : ForbiddenEHNWitness F Target,
          v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
            t.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) := by
        intro t
        exact hBound.trans (hMin t)
      have hRootInjOn : Set.InjOn v.toTarget
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) v.toTarget) := by
        intro a _ b _ hSame
        exact hInjective hSame
      obtain ⟨P, hSmallest⟩ :=
        minimalGlobalForbiddenWitness_exists_minimalMixedPiece_of_rootInjOn
          F hFiniteF hConnected
          Target Left Right jLeft jRight X iLeft iRight
          hTargetFree hCommon hAvoidLeft hAvoidRight
          v hMinimalV hRootInjOn
      exact ⟨w, hMin, Or.inr (Or.inr
        ⟨v, hInjective, hMinimalV, P, hSmallest⟩)⟩
    · have hBadRelation :
          ∃ (R : L.RelSymbol) (zs : Fin (L.relArity R) → UT),
            (∀ i, zs i ∈ Set.range w.toTarget) ∧
            Target.rel R zs ∧
            ¬ ∃ ys : Fin (L.relArity R) → w.Carrier,
              w.source.rel R ys ∧ zs = w.toTarget ∘ ys := by
        by_contra hNo
        apply hRelations
        intro R zs hRange hTarget
        by_contra hMissing
        exact hNo ⟨R, zs, hRange, hTarget, hMissing⟩
      obtain ⟨R, zs, hRange, hTarget, hMissing⟩ := hBadRelation
      let xs : Fin (L.relArity R) → w.Carrier :=
        fun i => Classical.choose (hRange i)
      have hArgs : w.toTarget ∘ xs = zs := by
        funext i
        exact Classical.choose_spec (hRange i)
      have hTargetInput : Target.rel R (w.toTarget ∘ xs) := by
        rw [hArgs]
        exact hTarget
      have hNoSourceInput : ¬ w.source.rel R xs := by
        intro hSource
        exact hMissing ⟨xs, hSource, hArgs.symm⟩
      have hUncovered :
          ¬ RelationInputCoveredByFullIrreducibleTest w.source R xs := by
        intro hCovered
        have hSource :=
          ehn_localRelationInputCover_reflectsTargetPositive
            w.source Target w.toTarget w.homEmbedding
            R xs hCovered hTargetInput
        exact hNoSourceInput hSource
      obtain ⟨dec, hCross⟩ :=
        uncoveredRelationInput_hasCrossingFreeDecomposition
          w.source R xs hUncovered
      exact ⟨w, hMin, Or.inr (Or.inl
        ⟨R, xs, hTargetInput, hNoSourceInput, dec, hCross⟩)⟩
  · have hBadFunction :
        ∃ (G : L.FuncSymbol)
            (zs : Fin (L.funcArity G) → UT) (z : UT),
          (∀ i, zs i ∈ Set.range w.toTarget) ∧
          z ∈ Target.func G zs ∧
          ¬ ∃ (ys : Fin (L.funcArity G) → w.Carrier)
                (out : w.Carrier),
            out ∈ w.source.func G ys ∧
            zs = w.toTarget ∘ ys ∧ z = w.toTarget out := by
      by_contra hNo
      apply hFunction
      intro G zs z hRange hTarget
      by_contra hMissing
      exact hNo ⟨G, zs, z, hRange, hTarget, hMissing⟩
    obtain ⟨G, zs, z, hRange, hPos, hNoLift⟩ := hBadFunction
    let xs : Fin (L.funcArity G) → w.Carrier :=
      fun i => Classical.choose (hRange i)
    have hArgs : w.toTarget ∘ xs = zs := by
      funext i
      exact Classical.choose_spec (hRange i)
    have hTargetInput : z ∈ Target.func G (w.toTarget ∘ xs) := by
      rw [hArgs]
      exact hPos
    have hNoLiftAtXs :
        ¬ ∃ (ys : Fin (L.funcArity G) → w.Carrier)
              (out : w.Carrier),
          out ∈ w.source.func G ys ∧
          w.toTarget ∘ ys = w.toTarget ∘ xs ∧
          w.toTarget out = z := by
      rintro ⟨ys, out, hValue, hCoords, hOutput⟩
      exact hNoLift
        ⟨ys, out, hValue, hArgs.symm.trans hCoords.symm,
          hOutput.symm⟩
    have hNoValue :
        z ∉ imageSet w.toTarget (w.source.func G xs) := by
      rintro ⟨out, hValue, hOutput⟩
      exact hNoLiftAtXs ⟨xs, out, hValue, rfl, hOutput⟩
    have hUncovered :
        ¬ FunctionInputCoveredByFullIrreducibleTest w.source G xs := by
      intro hCovered
      exact hNoValue
        (ehn_localFunctionInputCover_liftsTargetOutput
          w.source Target w.toTarget w.homEmbedding
          G xs hCovered z hTargetInput)
    obtain ⟨dec⟩ :=
      uncoveredFunctionInput_generatedClosedHull_decomposes
        w.source G xs hUncovered
    have hCross :=
      generatedClosedHull_properFreeDecomposition_inputsCross
        w.source xs dec
    exact ⟨w, hMin, Or.inl
      ⟨G, xs, z, hTargetInput, hNoLiftAtXs, dec, hCross⟩⟩

end AllThoseRamseyClasses.Lifts
