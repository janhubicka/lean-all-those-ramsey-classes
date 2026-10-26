import AllThoseRamseyClasses.Applications.MetricLocalClosureCoherence

/-!
# Exact finite induced support for locally forced metric F_j closures

The printed exact-local-completion condition ranges over WEAK
INDUCED SUBSETS of a candidate structure, not an embedding of
the entire candidate into a valid target. Thus the hypothesis
of a globally injective completion map in the preceding edge
lemma is stronger than a genuine finite local test.

This file keeps the ORIGINAL candidate carrier A and allows an
arbitrary total extension i : A → V of a local completion map.
Injectivity is demanded ONLY on the tested finite support,
while exact preservation of F_j is demanded ONLY on its two
short-edge endpoints. We need no metric or injectivity
assertion outside that tested support.

The appropriate support for an edge (x,y) consists of
the two endpoints and their two candidate F_j closure
representatives. The resulting equality follows from the
literal target closure law and maps back by injectivity on
that support. It is the source-faithful local ingredient
needed before assembling any path-compression and numerical
cutoff argument.

This does NOT prove that every such four-element support is
one of the printed weak induced substructures, or that
the manuscript's original uniform n bound suffices:
those remain separate proof obligations.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- A j-short edge in one valid target forces the old
closure representatives equal, even when the completion
map is injective ONLY on a named tested support. -/
theorem metricClosureRepresentative_eq_of_supported_local_completion
    {S : Set ℝ}
    (hpos : Positive S)
    {A : Type u} {V : Type v} [LinearOrder V]
    (i : A → V)
    (T : Set A)
    (hInj : Set.InjOn i T)
    (fA : A → Option A) (fV : V → Option V)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    (j : ℝ) (hj : Jump S j)
    (hLawV : MetricJumpClosureLaw dV fV j)
    (x y : A)
    (hMemX : metricClosureRepresentative fA x ∈ T)
    (hMemY : metricClosureRepresentative fA y ∈ T)
    (hShort : dV (i x) (i y) ≤ j)
    (hExactX : fV (i x) = Option.map i (fA x))
    (hExactY : fV (i y) = Option.map i (fA y)) :
    metricClosureRepresentative fA x =
      metricClosureRepresentative fA y := by
  apply hInj hMemX hMemY
  calc
    i (metricClosureRepresentative fA x) =
        metricClosureRepresentative fV (i x) :=
      (metricClosureRepresentative_map_of_exact_value
        i fA fV x hExactX).symm
    _ = metricClosureRepresentative fV (i y) :=
      metricClosureRepresentative_eq_of_close
        hpos hdV j hj fV hLawV (i x) (i y) hShort
    _ = i (metricClosureRepresentative fA y) :=
      metricClosureRepresentative_map_of_exact_value
        i fA fV y hExactY

/-- The full candidate need not embed: injectivity only
on the two endpoints and their two named closure
representatives suffices. This is the canonical
FOUR-VERTEX support of a short-edge local test. -/
theorem metricClosureRepresentative_eq_of_four_point_completion
    {S : Set ℝ}
    (hpos : Positive S)
    {A : Type u} {V : Type v} [LinearOrder V]
    (i : A → V)
    (fA : A → Option A) (fV : V → Option V)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    (j : ℝ) (hj : Jump S j)
    (hLawV : MetricJumpClosureLaw dV fV j)
    (x y : A)
    (hInj : Set.InjOn i
      ({x, y, metricClosureRepresentative fA x,
        metricClosureRepresentative fA y} : Set A))
    (hShort : dV (i x) (i y) ≤ j)
    (hExactX : fV (i x) = Option.map i (fA x))
    (hExactY : fV (i y) = Option.map i (fA y)) :
    metricClosureRepresentative fA x =
      metricClosureRepresentative fA y := by
  apply metricClosureRepresentative_eq_of_supported_local_completion
    hpos i
    ({x, y, metricClosureRepresentative fA x,
      metricClosureRepresentative fA y} : Set A)
    hInj fA fV hdV j hj hLawV x y
  · simp
  · simp
  · exact hShort
  · exact hExactX
  · exact hExactY

end AllThoseRamseyClasses.Applications.MetricSaturation
