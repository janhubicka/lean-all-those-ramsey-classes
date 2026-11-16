import AllThoseRamseyClasses.Lifts.Claim2OriginalMixedPieceInitialQStep
import AllThoseRamseyClasses.Lifts.EHNLocalMinimalWitnessMixedPiece

/-!
# Track B/D: local native source-test reflection gives an ACTUAL first Q-step

The Track D original finite forbidden EHN source theorem already
provides, under local source-input FULL irreducible-test coverage
and target relation tuple reflection on ONE globally A-support-minimal
weak witness, a genuine injective finite forbidden replacement
and its smallest mixed native positive-width geometric source piece.

An injective original weak EHN source map is, in particular,
injective on its selected outer ordered root TARGET coordinates
and on EVERY complete function-generated B-active source boundary.
The new Track B initial mixed-piece theorem can therefore be
applied to precisely the same injective replacement witness,
proving a genuine A-free SAME forbidden selected Q+old-E
full native source flip. The selected Q, whole source and
weak target map are literal; no new quotient or arbitrary Q.

This establishes a useful conditional LOCAL source-test
initialization route (one actual weak witness), rather than
assuming arbitrary weak maps are injective or that the printed
2019 global canonical lift itself proves the local reflection
hypotheses. It does NOT propagate global A-minimality through
the first flip, eliminate all source-test gaps, or prove
unrestricted original Claim 2 / strong AP.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- ONE actual original globally A-SOURCE-minimal forbidden weak
EHN witness with locally FULL-tested function inputs and source
relation reflection on its target range can be replaced by an
ACTUAL injective globally A-minimal finite forbidden source/map.
For the smallest genuinely mixed geometric separator P of THAT
same source, root and ALL active B-boundary target injections
follow from whole-source injectivity, so the new all-width
Track B/C extremal theorem constructs ONE genuine A-free
same-selected-Q native B→A replacement.

No global source-test covering assumption on the entire family F
is used, beyond the named printed tuple-surjective forbidden-image
closure hImage. No selected Q is assumed A-neutral. -/
theorem claim2_localSourceReflection_globalAMinimal_hasActualFirstSelectedQ
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
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hAvoidLeft : AvoidsGlobalFunctionalEHN F Left)
    (hAvoidRight : AvoidsGlobalFunctionalEHN F Right)
    (w : ForbiddenEHNWitness F Target)
    (hOriginalAMin :
      ∀ z : ForbiddenEHNWitness F Target,
        w.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        z.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft))
    (hInputCover :
      FunctionInputTuplesCoveredByIrreducibleTests w.source)
    (hRelationRange :
      SourceRelationTuplesCoveredOnRange
        w.source Target w.toTarget) :
    ∃ (v : ForbiddenEHNWitness F Target),
      Function.Injective v.toTarget ∧
      (∀ z : ForbiddenEHNWitness F Target,
        v.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        z.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
      ∃ P : MixedGeometricPiece v.source
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) v.toTarget)
          (weakFreeLeftPart (sL := iLeft) (iL := jLeft) v.toTarget)
          (weakFreeRightPart
            (sL := iLeft) (iL := jLeft)
            (iR := jRight) v.toTarget),
        (∀ Q : MixedGeometricPiece v.source
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) v.toTarget)
          (weakFreeLeftPart (sL := iLeft) (iL := jLeft) v.toTarget)
          (weakFreeRightPart
            (sL := iLeft) (iL := jLeft)
            (iR := jRight) v.toTarget),
          P.nonrootCount ≤ Q.nonrootCount) ∧
        ∃ (hRootInj : Function.Injective
              (fun i : Fin P.width =>
                v.toTarget (P.data.roots i)))
          (hBoundaryInj :
            ∀ (x : {a : v.Carrier //
                a ∉ weakFreeRootPart
                  (sL := iLeft) (iL := jLeft) v.toTarget}),
              x.1 ∈ geometricPieceVertices v.source P.data →
              x.1 ∈ weakFreeRightPart
                (sL := iLeft) (iL := jLeft)
                (iR := jRight) v.toTarget →
              Set.InjOn v.toTarget
                (v.source.functionClosure
                  (gaifmanNeighborhood v.source.graph
                    (componentFrom v.source.graph
                      (weakFreeRootPart
                        (sL := iLeft) (iL := jLeft)
                        v.toTarget) x))))
          (t : Claim2NativeGeometricState F Target Left Right
            jLeft jRight X iLeft iRight P.width),
          claim2NativeAFreeSelectedQStep F Target Left Right
            jLeft jRight X iLeft iRight P.positive
            (claim2NativeGeometricState_ofMixedOriginalPiece
              F Target Left Right jLeft jRight X iLeft iRight
              v P hRootInj hBoundaryInj) t := by
  classical
  obtain ⟨v, hVInjective, hVAMin, P, hPMixedMinimal⟩ :=
    minimalForbiddenWitness_localRangeReflection_yields_injectiveMinimalMixedPiece
      F hFiniteF hConnected hImage
      Target Left Right jLeft jRight X iLeft iRight
      hFree hCommon hAvoidLeft hAvoidRight
      w hOriginalAMin hInputCover hRelationRange
  have hRootInj :
      Function.Injective
        (fun i : Fin P.width =>
          v.toTarget (P.data.roots i)) := by
    intro i j hij
    exact P.data.roots_injective (hVInjective hij)
  have hBoundaryInj :
      ∀ (x : {a : v.Carrier //
          a ∉ weakFreeRootPart
            (sL := iLeft) (iL := jLeft) v.toTarget}),
        x.1 ∈ geometricPieceVertices v.source P.data →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft)
          (iR := jRight) v.toTarget →
        Set.InjOn v.toTarget
          (v.source.functionClosure
            (gaifmanNeighborhood v.source.graph
              (componentFrom v.source.graph
                (weakFreeRootPart
                  (sL := iLeft) (iL := jLeft)
                  v.toTarget) x))) := by
    intro x _hxOuter _hxB a _ha b _hb hab
    exact hVInjective hab
  obtain ⟨t, hSelectedQ⟩ :=
    claim2_originalAMinimal_smallestMixedPiece_hasActualAFreeQStep
      F hFiniteF hConnected
      Target Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      v hVAMin P hPMixedMinimal
      hRootInj hBoundaryInj
  exact ⟨v, hVInjective, hVAMin, P, hPMixedMinimal,
    hRootInj, hBoundaryInj, t, hSelectedQ⟩

end AllThoseRamseyClasses.Lifts
