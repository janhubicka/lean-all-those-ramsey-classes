import AllThoseRamseyClasses.Lifts.EHNUnliftableIncidenceFreeSide
import AllThoseRamseyClasses.Lifts.EHNExactTargetIncidenceTrichotomy

/-!
# Track D: exact all-preimage nonliftability localized to genuine target sides

The source-generated weak quotient is tuple-surjective, but need not
embed fully in the native target. The verified #1046 analysis separated
exact positive target incidence coverage from source test coverage;
however, its published relation-defect output retained only one
missing original source relation tuple, despite obtaining an
all-preimage nonliftability certificate internally.

This module runs the exact native range-coverage dichotomy directly.
For a globally left-SOURCE-support-minimal forbidden EHN witness in
the ACTUAL full native free amalgam of forbidden-free sides carrying
the common complete ORIGINAL 2019 canonical lift, it proves that:

* an ACTUAL positive target function incidence has NO positive
  source incidence lift at ANY matching input/output coordinates,
  and is wholly supported in one genuine FULL target side; OR
* an ACTUAL positive target old relation tuple has NO positive
  source relation lift at ANY matching input coordinates, and is
  wholly supported in one genuine FULL target side; OR
* the printed tuple-surjective image-closure contract produces
  an injective globally left-SOURCE-support-minimal forbidden
  witness and its genuine smallest mixed geometric piece.

In the first two alternatives the corresponding ACTUAL source
input-generated function-closed hull has a proper FULL native free
decomposition, with neither proper side containing all generators.
These source hull sides are NOT the target free-amalgam sides.

This is an exhaustive source-matched proof-control reduction.
The positive target side incidences are NOT shown to contradict
the common canonical global lift. A crossed input-generated hull
is NOT automatically a selected geometric forbidden subpiece.
The original unrestricted strong AP and Claim 2 remain OPEN.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A positive target native function incidence at original source image
inputs with NO positive source lift at ANY matching input/output
coordinates forces EVERY matching original source input tuple to
have an EMPTY whole function-value fibre.

If a matching source input had even one old function output, the
full function-closed hull of that DEFINED input would be irreducible.
The original EHN test clause then reflects every target output
at those coordinates to a positive source output, contradicting
global nonliftability.

This is stronger than saying one representative source input has
no value, and requires no maximal lift or forbidden-family closure.
-/
theorem ehn_unliftableFunction_allSourcePreimageFibresEmpty
    {V UT : Type}
    (Source : Structure L V) (Target : Structure L UT)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (G : L.FuncSymbol)
    (xs : Fin (L.funcArity G) → V)
    (z : UT)
    (hTarget : z ∈ Target.func G (f ∘ xs))
    (hNoLift : ¬ ∃ (ys : Fin (L.funcArity G) → V) (out : V),
      out ∈ Source.func G ys ∧
      f ∘ ys = f ∘ xs ∧ f out = z) :
    ∀ ys : Fin (L.funcArity G) → V,
      f ∘ ys = f ∘ xs → Source.func G ys = ∅ := by
  intro ys hCoords
  ext out
  constructor
  · intro hPositive
    have hCovered :
        FunctionInputCoveredByFullIrreducibleTest Source G ys :=
      functionInputCovered_of_positiveSourceFunctionValue
        Source G ys ⟨out, hPositive⟩
    have hTargetYs : z ∈ Target.func G (f ∘ ys) := by
      rw [hCoords]
      exact hTarget
    obtain ⟨v, hv, hvImage⟩ :=
      ehn_localFunctionInputCover_liftsTargetOutput
        Source Target f hf G ys hCovered z hTargetYs
    exact False.elim (hNoLift ⟨ys, v, hv, hCoords, hvImage⟩)
  · intro h
    exact False.elim h

/-- An ACTUAL positive target function incidence on original SOURCE
image coordinates with no positive original source lift at ANY
matching input and output coordinates, supported completely in
one FULL target side, with the original input-generated source
hull crossing a genuine FULL native free decomposition. -/
def HasFullSideUnliftableFunctionIncident
    {V UA UB UT : Type}
    (Source : Structure L V)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (jL : Structure.Embedding Left Target)
    (jR : Structure.Embedding Right Target)
    (f : V → UT) : Prop :=
  ∃ (G : L.FuncSymbol)
      (xs : Fin (L.funcArity G) → V) (z : UT),
    z ∈ Target.func G (f ∘ xs) ∧
    (¬ ∃ (ys : Fin (L.funcArity G) → V) (out : V),
      out ∈ Source.func G ys ∧
      f ∘ ys = f ∘ xs ∧ f out = z) ∧
    (∀ ys : Fin (L.funcArity G) → V,
      f ∘ ys = f ∘ xs → Source.func G ys = ∅) ∧
    SourceInputHasCrossingNativeHull Source xs ∧
    ((∃ (ys : Fin (L.funcArity G) → UA) (out : UA),
      out ∈ Left.func G ys ∧
      f ∘ xs = jL ∘ ys ∧ z = jL out) ∨
     (∃ (ys : Fin (L.funcArity G) → UB) (out : UB),
      out ∈ Right.func G ys ∧
      f ∘ xs = jR ∘ ys ∧ z = jR out))

/-- The corresponding relation defect has no original POSITIVE
source lift at ANY matching source input tuple, not merely at the
chosen representative source input. This is stronger than the
relation branch exported in the verified #1046 result. -/
def HasFullSideUnliftableRelationIncident
    {V UA UB UT : Type}
    (Source : Structure L V)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (jL : Structure.Embedding Left Target)
    (jR : Structure.Embedding Right Target)
    (f : V → UT) : Prop :=
  ∃ (R : L.RelSymbol) (xs : Fin (L.relArity R) → V),
    Target.rel R (f ∘ xs) ∧
    (¬ ∃ ys : Fin (L.relArity R) → V,
      Source.rel R ys ∧ f ∘ ys = f ∘ xs) ∧
    SourceInputHasCrossingNativeHull Source xs ∧
    ((∃ ys : Fin (L.relArity R) → UA,
      Left.rel R ys ∧ f ∘ xs = jL ∘ ys) ∨
     (∃ ys : Fin (L.relArity R) → UB,
      Right.rel R ys ∧ f ∘ xs = jR ∘ ys))

/-- The fully global-no-lift, actual target-side-localized
incidence-or-smallest-mixed-piece trichotomy under the ORIGINAL
printed tuple-surjective family image-closure contract.

No source irreducible-test input COVER premise is assumed. Target
incidences are localized through the genuine FULL native free
amalgam, and BOTH negative alternatives rule out EVERY original
positive source lift at the exact target coordinates.

The original maximal-common-lift hypotheses appear explicitly;
they are NOT used to postulate the absence of the two defects. -/
theorem exists_minimalForbiddenWitness_fullyUnliftableSideIncidence_or_mixedPiece
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
      (HasFullSideUnliftableFunctionIncident
          w.source Left Right Target jLeft jRight w.toTarget ∨
       HasFullSideUnliftableRelationIncident
          w.source Left Right Target jLeft jRight w.toTarget ∨
       ∃ (v : ForbiddenEHNWitness F Target),
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
             P.nonrootCount ≤ Q.nonrootCount) := by
  classical
  obtain ⟨w, hMin⟩ :=
    exists_minimalForbiddenEHNWitness_support F Target
      (fullFreeLeftExclusiveTarget iLeft jLeft) hExists
  by_cases hFunction :
      SourceFunctionValueTuplesCoveredOnRange w.source Target w.toTarget
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
      have hNoLift :
          ¬ ∃ ys : Fin (L.relArity R) → w.Carrier,
            w.source.rel R ys ∧
            w.toTarget ∘ ys = w.toTarget ∘ xs := by
        rintro ⟨ys, hPositive, hCoords⟩
        exact hMissing ⟨ys, hPositive,
          hArgs.symm.trans hCoords.symm⟩
      obtain ⟨hCross, hSide⟩ :=
        ehn_unliftableRelation_liesInFullSide_withSourceCrossingHull
          w.source X Left Right Target
          iLeft iRight jLeft jRight hTargetFree
          w.toTarget w.homEmbedding R xs hTargetInput hNoLift
      exact ⟨w, hMin, Or.inr (Or.inl
        ⟨R, xs, hTargetInput, hNoLift, hCross, hSide⟩)⟩
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
    obtain ⟨G, zs, z, hRange, hTarget, hMissing⟩ := hBadFunction
    let xs : Fin (L.funcArity G) → w.Carrier :=
      fun i => Classical.choose (hRange i)
    have hArgs : w.toTarget ∘ xs = zs := by
      funext i
      exact Classical.choose_spec (hRange i)
    have hTargetInput : z ∈ Target.func G (w.toTarget ∘ xs) := by
      rw [hArgs]
      exact hTarget
    have hNoLift :
        ¬ ∃ (ys : Fin (L.funcArity G) → w.Carrier)
              (out : w.Carrier),
          out ∈ w.source.func G ys ∧
          w.toTarget ∘ ys = w.toTarget ∘ xs ∧
          w.toTarget out = z := by
      rintro ⟨ys, out, hValue, hCoords, hOutput⟩
      exact hMissing
        ⟨ys, out, hValue, hArgs.symm.trans hCoords.symm,
          hOutput.symm⟩
    obtain ⟨hCross, hSide⟩ :=
      ehn_unliftableFunction_liesInFullSide_withSourceCrossingHull
        w.source X Left Right Target
        iLeft iRight jLeft jRight hTargetFree
        w.toTarget w.homEmbedding G xs z hTargetInput hNoLift
    have hAllUndefined :=
      ehn_unliftableFunction_allSourcePreimageFibresEmpty
        w.source Target w.toTarget w.homEmbedding
        G xs z hTargetInput hNoLift
    exact ⟨w, hMin, Or.inl
      ⟨G, xs, z, hTargetInput, hNoLift,
        hAllUndefined, hCross, hSide⟩⟩

end AllThoseRamseyClasses.Lifts
