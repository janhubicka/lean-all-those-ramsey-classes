import AllThoseRamseyClasses.Lifts.EHNUnliftableIncidenceFreeSide
import AllThoseRamseyClasses.Lifts.EHNExactTargetIncidenceTrichotomy

/-!
# Track D: complete actual target-side localization of the Section 3 incidence trichotomy

The verified minimal forbidden EHN source obstruction theorem #1046
produces an ACTUAL target-only native positive function incidence or
positive old relation at original source image inputs, or else an
injective source-support-minimal forbidden witness with a genuinely
smallest mixed piece.

In a genuine FULL target free amalgam, every positive relation or
function-value incidence belongs to a real FULL embedded side. The
new source-localized witnesses make that fact explicit at the SAME
target coordinates as the original forbidden source map and retain
the ACTUAL crossed FULL native source input-generated hull.

The relation alternative retains exactly the conclusion of merged
#1046: its displayed source input has no old relation. It does
NOT silently strengthen this to absence of ALL OTHER possible
source relation input tuples at the same target coordinates.
The function alternative does have the stronger global no-lift
property (at any source input representative), as in #1046.

Neither side-locality nor the source hull crossing proves that
the common original canonical lift excludes this obstruction.
The outer root / selected-Q geometric flips and Claim 2 remain
independent.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An ACTUAL positive target function incidence at original source
image inputs that has NO positive source lift at ANY matching
preimage tuple, together with a genuine two-sided FULL native
crossing source hull, is supported wholly in a target side.
The original source map may have arbitrary collisions. -/
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
    SourceInputHasCrossingNativeHull Source xs ∧
    ((∃ (ys : Fin (L.funcArity G) → UA) (out : UA),
      out ∈ Left.func G ys ∧
      f ∘ xs = jL ∘ ys ∧ z = jL out) ∨
     (∃ (ys : Fin (L.funcArity G) → UB) (out : UB),
      out ∈ Right.func G ys ∧
      f ∘ xs = jR ∘ ys ∧ z = jR out))

/-- An ACTUAL positive target OLD relation at selected original
source image input coordinates that is absent on this SAME source
input, together with the crossed FULL native source hull, belongs
to an actual FULL target side. This local predicate does NOT
claim no OTHER source tuple at the target coordinates is positive. -/
def HasFullSideExtraRelationIncident
    {V UA UB UT : Type}
    (Source : Structure L V)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (jL : Structure.Embedding Left Target)
    (jR : Structure.Embedding Right Target)
    (f : V → UT) : Prop :=
  ∃ (R : L.RelSymbol) (xs : Fin (L.relArity R) → V),
    Target.rel R (f ∘ xs) ∧
    ¬ Source.rel R xs ∧
    SourceInputHasCrossingNativeHull Source xs ∧
    ((∃ ys : Fin (L.relArity R) → UA,
      Left.rel R ys ∧ f ∘ xs = jL ∘ ys) ∨
     (∃ ys : Fin (L.relArity R) → UB,
      Right.rel R ys ∧ f ∘ xs = jR ∘ ys))

/-- The source-matched exact 2019 obstruction trichotomy, promoted
to the GENUINE full target sides without using ANY global
source irreducible input cover.

For every forbidden EHN witness in the actual full free amalgam of
F-free structures with a common original full global canonical
lift, choose a witness w minimizing ORIGINAL SOURCE left-exclusive
support. Then either:

1. a positive target function incidence with NO lift from ANY
   original source matching input tuple is located entirely on
   one FULL target side; its actual original source input hull
   has a proper FULL crossing decomposition;
2. a positive target old relation on original source coordinates,
   missing on those original source coordinates, lies inside one
   FULL target side with an actual crossing source hull; or
3. there is an injective source-support-minimal forbidden witness
   with an actual smallest genuine MIXED geometric piece.

The first two alternatives are not contradicted by F-freeness of
the sides alone, and the last does not complete Claim 2. -/
theorem exists_minimalForbiddenWitness_sideLocalTargetDefect_or_mixedPiece
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
       HasFullSideExtraRelationIncident
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
  obtain ⟨w, hMin, hCases⟩ :=
    exists_minimalForbiddenWitness_targetIncidenceDefect_or_mixedPiece
      F hFiniteF hConnected hImage
      Target Left Right jLeft jRight
      X iLeft iRight hTargetFree hCommon
      hAvoidLeft hAvoidRight hExists
  refine ⟨w, hMin, ?_⟩
  rcases hCases with hFunction | hRelation | hMixed
  · obtain ⟨G, xs, z, hPositive, hNoLift, d, hCross⟩ := hFunction
    obtain ⟨hGenerated, hSide⟩ :=
      ehn_unliftableFunction_liesInFullSide_withSourceCrossingHull
        w.source X Left Right Target
        iLeft iRight jLeft jRight hTargetFree
        w.toTarget w.homEmbedding G xs z hPositive hNoLift
    exact Or.inl ⟨G, xs, z, hPositive, hNoLift, hGenerated, hSide⟩
  · obtain ⟨R, xs, hPositive, hMissing, d, hCross⟩ := hRelation
    have hGenerated : SourceInputHasCrossingNativeHull w.source xs :=
      ⟨d, hCross⟩
    have hSide :=
      (hTargetFree.rel_iff R (w.toTarget ∘ xs)).mp hPositive
    exact Or.inr (Or.inl
      ⟨R, xs, hPositive, hMissing, hGenerated, hSide⟩)
  · exact Or.inr (Or.inr hMixed)

end AllThoseRamseyClasses.Lifts
