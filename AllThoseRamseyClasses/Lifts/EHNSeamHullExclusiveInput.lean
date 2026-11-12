import AllThoseRamseyClasses.Lifts.EHNCrossingHullFullSideFactor
import AllThoseRamseyClasses.Lifts.WeakSourceFreeAmalgamPartition

/-!
# Track D: common-seam source hull or an actual exclusive source input

For an original EHN map into a GENUINE FULL native free amalgam,
choose any family of source generators. There are two exact cases:

1. EVERY generator maps into the common full root seam. The entire
   native function-closed original source hull then has a genuine
   EHN factor into that very common root (not merely one side).
2. An ACTUAL source generator has image outside the common seam,
   and hence is in one of the exact left/right exclusive source
   regions of the original full free-amalgam partition.

When the selected source inputs witness a globally unliftable
positive target native function incidence, in the first case
the target FUNCTION OUTPUT must also lie in the common full
root seam, because the root is function-closed. For relations
the entire tuple lies in the seam.

The generated source hull may still have an ACTUAL proper FULL
free decomposition crossed by its generators. This is a source-
geometric classification only; neither case is ruled out by
maximal common canonical-lift compatibility in the present proof.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every original source input tuple under an EHN map into the
actual full native free amalgam has a strict dichotomy:

* all its source input vertices map into the complete common-root
  seam, and their ENTIRE function-closed generated source hull
  genuinely factors EHN into the full common Root; or
* at least one ACTUAL original source input vertex is left- or
  right-exclusive relative to the common root.

No input positive incidence, root-image injectivity, selected
forbidden piece, finite carrier or forbidden-family assumption. -/
theorem ehn_sourceInputHull_commonRootOrExclusiveGenerator
    {V UX UA UB UT X : Type}
    (Source : Structure L V)
    (Root : Structure L UX)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (sL : Structure.Embedding Root Left)
    (sR : Structure.Embedding Root Right)
    (jL : Structure.Embedding Left Target)
    (jR : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam sL sR jL jR)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (xs : X → V) :
    (((∀ i : X, f (xs i) ∈ Set.range (jL.comp sL)) ∧
      ∃ q : Source.functionClosure (Set.range xs) → UX,
        (Source.induce (Source.functionClosure (Set.range xs))
          (Source.functionClosure_isClosed (Set.range xs))).
            IsEHNHomomorphismEmbedding Root q ∧
        ∀ z : Source.functionClosure (Set.range xs),
          (jL.comp sL) (q z) = f z.1) ∨
     (∃ i : X,
       xs i ∈ weakFreeLeftPart (sL := sL) (iL := jL) f ∨
       xs i ∈ weakFreeRightPart
         (sL := sL) (iL := jL) (iR := jR) f)) := by
  classical
  by_cases hRoot : ∀ i : X, f (xs i) ∈ Set.range (jL.comp sL)
  · obtain ⟨q, hq, hCoords⟩ :=
      ehn_generatedClosedHull_factors_fullSide
        Source Root Target f hf (jL.comp sL) xs hRoot
    exact Or.inl ⟨hRoot, q, hq, hCoords⟩
  · have hOutside :
        ∃ i : X, f (xs i) ∉ Set.range (jL.comp sL) := by
      by_contra hNone
      apply hRoot
      intro i
      by_contra hi
      exact hNone ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hOutside
    rcases weakFreePartition_covers hFree f (xs i) with
        hSeam | hLeft | hRight
    · exact False.elim (hi hSeam)
    · exact Or.inr ⟨i, Or.inl hLeft⟩
    · exact Or.inr ⟨i, Or.inr hRight⟩

/-- A genuinely positive target native function incidence on
original source image coordinates is either fully seam-supported
(inputs AND output in the common FULL root) with an EHN
source input-hull factorization into that root, or some
original SOURCE function-input vertex lies in an exclusive region.

The target OUTPUT alone cannot escape the root when all
inputs are in it, since the root is native-function-closed.
This excludes the misleading "only the output is exclusive"
subcase in the no-source-lift analysis. -/
theorem ehn_positiveFunction_commonRootOrExclusiveSourceInput
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (Root : Structure L UX)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (sL : Structure.Embedding Root Left)
    (sR : Structure.Embedding Root Right)
    (jL : Structure.Embedding Left Target)
    (jR : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam sL sR jL jR)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (G : L.FuncSymbol)
    (xs : Fin (L.funcArity G) → V)
    (z : UT)
    (hPositive : z ∈ Target.func G (f ∘ xs)) :
    ((z ∈ Set.range (jL.comp sL) ∧
      (∀ i : Fin (L.funcArity G),
        f (xs i) ∈ Set.range (jL.comp sL)) ∧
      ∃ q : Source.functionClosure (Set.range xs) → UX,
        (Source.induce (Source.functionClosure (Set.range xs))
          (Source.functionClosure_isClosed (Set.range xs))).
            IsEHNHomomorphismEmbedding Root q ∧
        ∀ v : Source.functionClosure (Set.range xs),
          (jL.comp sL) (q v) = f v.1) ∨
     (∃ i : Fin (L.funcArity G),
       xs i ∈ weakFreeLeftPart (sL := sL) (iL := jL) f ∨
       xs i ∈ weakFreeRightPart
         (sL := sL) (iL := jL) (iR := jR) f)) := by
  rcases ehn_sourceInputHull_commonRootOrExclusiveGenerator
      Source Root Left Right Target
      sL sR jL jR hFree f hf xs with
      ⟨hRoot, q, hEHN, hCoords⟩ | hExclusive
  · have hOutputRoot : z ∈ Set.range (jL.comp sL) :=
      (jL.comp sL).range_isClosed G (f ∘ xs) hRoot hPositive
    exact Or.inl ⟨hOutputRoot, hRoot, q, hEHN, hCoords⟩
  · exact Or.inr hExclusive

/-- Every globally unliftable OLD positive relation tuple
in the actual native full free amalgam has a crossed original
source input-generated hull and fits the same source-side
common-seam factorization versus exclusive-source-vertex split.

The result does not pretend that the reducible common-seam hull
is a genuinely selected forbidden geometric piece. -/
theorem ehn_unliftableRelation_commonSeamHullOrExclusiveInput
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (Root : Structure L UX)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (sL : Structure.Embedding Root Left)
    (sR : Structure.Embedding Root Right)
    (jL : Structure.Embedding Left Target)
    (jR : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam sL sR jL jR)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (R : L.RelSymbol)
    (xs : Fin (L.relArity R) → V)
    (hPositive : Target.rel R (f ∘ xs))
    (hNoLift : ¬ ∃ ys : Fin (L.relArity R) → V,
      Source.rel R ys ∧ f ∘ ys = f ∘ xs) :
    SourceInputHasCrossingNativeHull Source xs ∧
    (((∀ i : Fin (L.relArity R),
        f (xs i) ∈ Set.range (jL.comp sL)) ∧
       ∃ q : Source.functionClosure (Set.range xs) → UX,
         (Source.induce (Source.functionClosure (Set.range xs))
           (Source.functionClosure_isClosed (Set.range xs))).
             IsEHNHomomorphismEmbedding Root q ∧
         ∀ z : Source.functionClosure (Set.range xs),
           (jL.comp sL) (q z) = f z.1) ∨
      (∃ i : Fin (L.relArity R),
        xs i ∈ weakFreeLeftPart (sL := sL) (iL := jL) f ∨
        xs i ∈ weakFreeRightPart
          (sL := sL) (iL := jL) (iR := jR) f)) := by
  obtain ⟨hCross, _hSide⟩ :=
    ehn_unliftableRelation_liesInFullSide_withSourceCrossingHull
      Source Root Left Right Target
      sL sR jL jR hFree f hf R xs hPositive hNoLift
  exact ⟨hCross, ehn_sourceInputHull_commonRootOrExclusiveGenerator
    Source Root Left Right Target sL sR jL jR hFree f hf xs⟩

/-- Every unliftable ACTUAL positive target function value
in the full free amalgam has a crossed native original source
input hull; either the entire target incidence is in the
complete shared root and the original source hull EHN-factors
into it, or a genuine source-input vertex maps exclusively
to one of the original two target sides. -/
theorem ehn_unliftableFunction_commonSeamHullOrExclusiveInput
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (Root : Structure L UX)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (sL : Structure.Embedding Root Left)
    (sR : Structure.Embedding Root Right)
    (jL : Structure.Embedding Left Target)
    (jR : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam sL sR jL jR)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (G : L.FuncSymbol)
    (xs : Fin (L.funcArity G) → V)
    (z : UT)
    (hPositive : z ∈ Target.func G (f ∘ xs))
    (hNoLift : ¬ ∃ (ys : Fin (L.funcArity G) → V) (out : V),
      out ∈ Source.func G ys ∧
      f ∘ ys = f ∘ xs ∧ f out = z) :
    SourceInputHasCrossingNativeHull Source xs ∧
    ((z ∈ Set.range (jL.comp sL) ∧
      (∀ i : Fin (L.funcArity G),
        f (xs i) ∈ Set.range (jL.comp sL)) ∧
      ∃ q : Source.functionClosure (Set.range xs) → UX,
        (Source.induce (Source.functionClosure (Set.range xs))
          (Source.functionClosure_isClosed (Set.range xs))).
            IsEHNHomomorphismEmbedding Root q ∧
        ∀ v : Source.functionClosure (Set.range xs),
          (jL.comp sL) (q v) = f v.1) ∨
     (∃ i : Fin (L.funcArity G),
       xs i ∈ weakFreeLeftPart (sL := sL) (iL := jL) f ∨
       xs i ∈ weakFreeRightPart
         (sL := sL) (iL := jL) (iR := jR) f)) := by
  obtain ⟨hCross, _hSide⟩ :=
    ehn_unliftableFunction_liesInFullSide_withSourceCrossingHull
      Source Root Left Right Target
      sL sR jL jR hFree f hf G xs z hPositive hNoLift
  exact ⟨hCross, ehn_positiveFunction_commonRootOrExclusiveSourceInput
    Source Root Left Right Target
    sL sR jL jR hFree f hf G xs z hPositive⟩

end AllThoseRamseyClasses.Lifts
