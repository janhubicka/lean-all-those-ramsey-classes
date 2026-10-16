import AllThoseRamseyClasses.Applications.MetricCanonicalFullOrderEmbedding
import AllThoseRamseyClasses.Applications.MetricCanonicalConvexity
import AllThoseRamseyClasses.Applications.MetricCompletedClosureFunctoriality
import AllThoseRamseyClasses.Applications.MetricCanonicalLiftUniqueness

/-!
# Paper-facing certificate for embeddings of finite canonical S-metric lifts

This exports the metric, ordered, and functional preservation components
of the paper's canonical lift together in one theorem, with no extra
axioms or synthetic class hypotheses. The canonical lift map is not
assumed to be an embedding: its injectivity, distance preservation,
order preservation and exact Option-valued function commutation are
all obtained from independently verified concrete proofs.

Uniqueness is established for *every* map extending the original
isometry and respecting the complete positive-jump closure functions:
there is no possibility to independently permute the new class tags.

This does not yet certify the class-level metric Ramsey theorem or
the corrected weak local-completion and strong-amalgamation axioms.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- Full source-matched components of a canonical finite metric
**ordered functional embedding**. The *target's* literal finite-S
paper-block convexity supplies the JumpConvex hypothesis needed for
insertion cuts. No convexity of a hypothetical intermediate image
is assumed. -/
theorem canonicalLift_finite_orderedFunctionalEmbedding {S : Set ℝ}
    {V : Type u} {W : Type v}
    [Finite V] [Finite W] [LinearOrder V] [LinearOrder W]
    (hfin : S.Finite)
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (hpaperW : PaperBlockConvex S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (hstrict : StrictMono f) :
    Function.Injective (mapCanonicalLift hpos hS hdV hdW f hf) ∧
      (∀ a b : V ⊕ CanonicalJumpTag hpos hS hdV,
        canonicalDistance hpos hS hdW
            (mapCanonicalLift hpos hS hdV hdW f hf a)
            (mapCanonicalLift hpos hS hdV hdW f hf b) =
          canonicalDistance hpos hS hdV a b) ∧
      (letI := canonicalInsertionLinearOrder hpos hS hdV;
        letI := canonicalInsertionLinearOrder hpos hS hdW;
        StrictMono (mapCanonicalLift hpos hS hdV hdW f hf)) ∧
      (∀ (j : PositiveJumpLevel S)
        (a : V ⊕ CanonicalJumpTag hpos hS hdV),
        Option.map (mapCanonicalLift hpos hS hdV hdW f hf)
            (canonicalCompletedClosureValue hpos hS hdV j a) =
          canonicalCompletedClosureValue hpos hS hdW j
            (mapCanonicalLift hpos hS hdV hdW f hf a)) := by
  have hsourceMetric :
      MetricOn S (canonicalDistance hpos hS hdV) :=
    canonicalDistance_metric hfin hpos hS hassoc hdV
  have hfour : FourValues S :=
    fourValues_of_associativeOn hpos hS hassoc
  have hconvW : JumpConvex S dW :=
    (paperBlockConvex_iff_jumpConvex hfin hpos hfour hdW).mp hpaperW
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mapCanonicalLift_injective hpos hS hassoc hdV hdW
      f hf hsourceMetric
  · exact mapCanonicalLift_isometry hpos hS hassoc hdV hdW f hf
  · exact canonicalInsertion_mapCanonicalLift_strictMono
      hpos hS hdV hdW hconvW f hf hstrict
  · exact mapCanonicalLift_preserves_completedClosureValue
      hpos hS hdV hdW f hf

/-- There is exactly one lifted vertex map extending an original
isometry and commuting with *all* completed partial jump-closure
values, whether or not that map was otherwise assumed to be metric
or order preserving. This is the uniqueness part of the paper's
metric embedding lemma stated using the **complete** function table. -/
theorem mapCanonicalLift_unique_of_completedClosure {S : Set ℝ}
    {V : Type u} {W : Type v}
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (g : (V ⊕ CanonicalJumpTag hpos hS hdV) →
      (W ⊕ CanonicalJumpTag hpos hS hdW))
    (hOld : ∀ x : V, g (.inl x) = .inl (f x))
    (hFunctions : ∀ (j : PositiveJumpLevel S)
      (a : V ⊕ CanonicalJumpTag hpos hS hdV),
      Option.map g (canonicalCompletedClosureValue hpos hS hdV j a) =
        canonicalCompletedClosureValue hpos hS hdW j (g a)) :
    g = mapCanonicalLift hpos hS hdV hdW f hf := by
  apply mapCanonicalLift_unique hpos hS hdV hdW f hf g hOld
  intro j x
  have h := hFunctions j (.inl x)
  simp only [canonicalCompletedClosureValue_old, Option.map_some,
    hOld x, Option.some.injEq] at h
  exact h

end AllThoseRamseyClasses.Applications.MetricSaturation
