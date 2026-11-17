import AllThoseRamseyClasses.Lifts.Claim2UncoveredInputCrossing
import AllThoseRamseyClasses.Lifts.Claim2SelectedClosedLexActualTradeoff
import AllThoseRamseyClasses.Lifts.Claim2GlobalLexSourceMinimizer

/-!
# Corrected EHN-image-closed Claim 2: exact first-state dichotomy

Under the STRONGER original-source assumption that the forbidden
family is closed under ACTUAL vertex-surjective EHN images,
the merged Track C proofs choose a global original
(A-exclusive SOURCE, B-exclusive SOURCE)-lex minimum,
injectivize it provided its actual range is function closed,
construct a genuine smallest mixed geometric separator
and obtain a REAL forbidden B-decreasing / A-increasing
same-target source replacement.

This theorem makes the SOURCE-LOCAL full irreducible
function-input test cover unnecessary as an assumption:
either the chosen global lex minimum has that cover
and the actual source replacement exists, OR an uncovered
native function-input tuple in THE SAME original lex
minimum has a proper FULL free decomposition of its
function-closed generated source hull, with inputs crossing
both decomposition sides.

This is the first-state obstruction dichotomy under the
stronger image closure, not the weaker printed tuple
closure. Neither branch alone contradicts lex minimality.
No original 2019 strong AP conclusion is asserted.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- For an actual full target free amalgam of F-EHN-free
left/right sides with a common original full canonical lift,
under TRUE vertex-surjective EHN image closure, one of:

(A) ONE genuine injective original lex-minimum witness admits
    an ACTUAL B-lowering and A-raising native forbidden source
    successor into that SAME target; or
(B) ONE original globally lex-minimal finite forbidden witness
    has a function input whose closed source hull admits a
    proper FULL free decomposition crossing both source sides.

No independent input-test coverage or target root injectivity
assumption; no false claim that the B-flipped source remains
global A-minimum. -/
theorem claim2_strongImage_globalLex_actualBAflip_or_functionCrossing
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hImageClosed :
      ∀ {W Z : Type}
        (Src : Structure L W) (Dst : Structure L Z)
        (q : W → Z),
        F Src →
        Src.IsEHNHomomorphismEmbedding Dst q →
        Function.Surjective q → F Dst)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
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
    (hNonempty : Nonempty (ForbiddenEHNWitness F Target)) :
    (∃ (v z : ForbiddenEHNWitness F Target),
      Function.Injective v.toTarget ∧
      z.sourceSupportCount
        (fullFreeRightExclusiveTarget iRight jRight) <
      v.sourceSupportCount
        (fullFreeRightExclusiveTarget iRight jRight) ∧
      v.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) <
      z.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft)) ∨
    (∃ w : ForbiddenEHNWitness F Target,
      (∀ z : ForbiddenEHNWitness F Target,
        w.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        z.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
      (∀ z : ForbiddenEHNWitness F Target,
        z.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) =
        w.sourceSupportCount
          (fullFreeLeftExclusiveTarget iLeft jLeft) →
        w.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) ≤
        z.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight)) ∧
      HasNativeFunctionInputCrossingHull w.source) := by
  classical
  obtain ⟨initial⟩ := hNonempty
  obtain ⟨W, New, hNew, hFiniteNew, g, hg,
      hMinA, hMinB⟩ :=
    exists_global_lex_minimum_weakForbiddenSource_support
      F hFiniteF Target initial.source initial.forbidden
      initial.toTarget initial.homEmbedding
      (fullFreeLeftExclusiveTarget iLeft jLeft)
      (fullFreeRightExclusiveTarget iRight jRight)
  let w : ForbiddenEHNWitness F Target := {
    Carrier := W
    finiteCarrier := hFiniteNew
    source := New
    forbidden := hNew
    toTarget := g
    homEmbedding := hg
  }
  have hOldA : ∀ z : ForbiddenEHNWitness F Target,
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
      z.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) := by
    intro z
    exact hMinA z.source z.forbidden z.toTarget z.homEmbedding
  have hOldB : ∀ z : ForbiddenEHNWitness F Target,
      z.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) =
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) →
      w.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight) ≤
      z.sourceSupportCount (fullFreeRightExclusiveTarget iRight jRight) := by
    intro z hEq
    exact hMinB z.source z.forbidden z.toTarget z.homEmbedding hEq
  by_cases hInput :
      FunctionInputTuplesCoveredByIrreducibleTests w.source
  · let hClosed : Target.IsClosed (Set.range w.toTarget) :=
      ehn_range_isClosed_of_irreducibleInputCover
        w.source Target w.toTarget w.homEmbedding hInput
    have hSelectedClosedLex :
        ∃ x : ForbiddenEHNWitness F Target,
          Target.IsClosed (Set.range x.toTarget) ∧
          (∀ z : ForbiddenEHNWitness F Target,
            x.sourceSupportCount
              (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
            z.sourceSupportCount
              (fullFreeLeftExclusiveTarget iLeft jLeft)) ∧
          (∀ z : ForbiddenEHNWitness F Target,
            z.sourceSupportCount
              (fullFreeLeftExclusiveTarget iLeft jLeft) =
            x.sourceSupportCount
              (fullFreeLeftExclusiveTarget iLeft jLeft) →
            x.sourceSupportCount
              (fullFreeRightExclusiveTarget iRight jRight) ≤
            z.sourceSupportCount
              (fullFreeRightExclusiveTarget iRight jRight)) :=
      ⟨w, hClosed, hOldA, hOldB⟩
    obtain ⟨v, hInj, hNewA, hNewB,
        z, hBdown, hAup⟩ :=
      exists_selectedClosedLex_actualFlip_strictGlobalBAtradeoff
        F hFiniteF hImageClosed hConnected
        Target Left Right jLeft jRight X iLeft iRight
        hFree hCommon hAvoidLeft hAvoidRight hSelectedClosedLex
    exact Or.inl ⟨v, z, hInj, hBdown, hAup⟩
  · exact Or.inr ⟨w, hOldA, hOldB,
      missingFunctionInputCover_hasCrossingHull w.source hInput⟩

end AllThoseRamseyClasses.Lifts
