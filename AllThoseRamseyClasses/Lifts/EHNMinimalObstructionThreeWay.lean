import AllThoseRamseyClasses.Lifts.EHNLocalMinimalWitnessMixedPiece
import AllThoseRamseyClasses.Lifts.EHNWeakImageUncoveredRelationInput
import AllThoseRamseyClasses.Lifts.EHNWeakImageUncoveredFunctionInput

/-!
# Track D: complete three-way source-geometric obstruction to injectivization

For the original 2019 family-level tuple-surjective image closure
and an ACTUAL full functional free amalgam with matching full global
canonical lifts, start from ANY forbidden EHN witness and choose
one minimizing the ORIGINAL source left-exclusive support.

Then there are three exact alternatives:

1. some original native function-input tuple of this minimal source
   has no full irreducible source test; its true input-generated
   closed source hull admits a proper FULL free decomposition;
2. some original target relation is positive on the image of this
   source, but not lifted by a positive original source tuple;
   chosen ACTUAL original source representatives of those target
   coordinates have an uncovered input-generated hull admitting
   a proper FULL free decomposition;
3. the same minimal source map satisfies both local range conditions,
   so the printed image closure constructs a support-minimal
   INJECTIVE forbidden witness and the verified Section 3 geometry
   produces its smallest genuine MIXED geometric piece.

No full-family input-test coverage is assumed. The theorem is a
source-matched reduction, NOT a proof that maximal common lifts
exclude (1)/(2), and not Claim 2 descent from (3).
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under ONLY the original global lift/free-amalgam hypotheses
and the paper-shaped tuple-surjective forbidden-image closure,
every nonempty forbidden weak EHN obstruction has a globally
left-source-support-minimal witness w with one of the following:

* an actual original source function input with no full
  irreducible test and a genuinely reducible full generated hull;
* an actual positive target relation on selected original
  source image coordinates, absent on that source input, whose
  full generated source hull is genuinely reducible;
* an actual INJECTIVE minimal forbidden witness v with its
  smallest genuine MIXED geometric piece.

This is a precise interface for a future maximal-lift proof:
exclude or resolve the two crossing-input cases, then Track C
must still supply the positive-rank mixed-piece descent. -/
theorem exists_minimalForbiddenWitness_with_crossingInput_or_mixedPiece
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W),
      F A → Finite W)
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
            (xs : Fin (L.funcArity G) → w.Carrier),
          ¬ FunctionInputCoveredByFullIrreducibleTest w.source G xs ∧
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
  by_cases hFunctionCover :
      FunctionInputTuplesCoveredByIrreducibleTests w.source
  · by_cases hRelations :
        SourceRelationTuplesCoveredOnRange w.source Target w.toTarget
    · obtain ⟨v, hInjective, hMinV, P, hSmallest⟩ :=
        minimalForbiddenWitness_localRangeReflection_yields_injectiveMinimalMixedPiece
          F hFiniteF hConnected hImage
          Target Left Right jLeft jRight X iLeft iRight
          hTargetFree hCommon hAvoidLeft hAvoidRight
          w hMin hFunctionCover hRelations
      exact ⟨w, hMin, Or.inr (Or.inr
        ⟨v, hInjective, hMinV, P, hSmallest⟩)⟩
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
            (xs : Fin (L.funcArity G) → w.Carrier),
          ¬ FunctionInputCoveredByFullIrreducibleTest w.source G xs := by
      by_contra hNo
      apply hFunctionCover
      intro G xs
      by_contra hMissing
      exact hNo ⟨G, xs, hMissing⟩
    obtain ⟨G, xs, hMissing⟩ := hBadFunction
    obtain ⟨dec⟩ :=
      uncoveredFunctionInput_generatedClosedHull_decomposes
        w.source G xs hMissing
    have hCross :=
      generatedClosedHull_properFreeDecomposition_inputsCross
        w.source xs dec
    exact ⟨w, hMin, Or.inl ⟨G, xs, hMissing, dec, hCross⟩⟩

end AllThoseRamseyClasses.Lifts
