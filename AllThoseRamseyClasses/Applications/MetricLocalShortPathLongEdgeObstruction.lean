import AllThoseRamseyClasses.Applications.MetricLocalClosurePathPropagation
import AllThoseRamseyClasses.Applications.MetricLocalClosureFourPointSupport
import AllThoseRamseyClasses.Applications.MetricClosureExactJumpQuotient

/-!
# Short functional paths exclude a directly prescribed long metric edge

The printed S-metric Ramsey proof uses paths whose edges lie in
a small-distance block. The earlier verified closure lemmas give
an exact local substitute for an unproved assertion that all
vertices of the path have a common designated F_j point.

This module proves a CONCRETE LOCAL OBSTRUCTION. If every short
edge of a candidate passes the specified four-vertex functional
completion test, the designated F_j closure representative is
constant along any finite short path. A separate valid local
completion at the two endpoint vertices must then put those
endpoints within distance j. It cannot preserve an explicitly
prescribed endpoint distance strictly greater than j.

The local edge maps are permitted to vary from edge to edge;
their injectivity is required only on the two endpoints and
their two named F_j closure representatives. A global candidate
embedding is NOT assumed.

Scope: each local target in this theorem has the same carrier,
metric and F_j law, although the individual completion maps may
differ. The weak-induced-substructure completion quantifiers of
the printed 2019 theorem and the numerical cutoff remain open.
No entire candidate metric or Ramsey conclusion is constructed.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- Under exact preservation of the two endpoint F_j values,
equality of their original closure representatives forces the
actual target metric distance to be at most j. No injectivity
outside these endpoint conditions is needed for this direction. -/
theorem metricClosureRepresentative_jump_close_of_local_endpoint_match
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {A : Type u} {V : Type v} [LinearOrder V]
    (i : A → V)
    (fA : A → Option A) (fV : V → Option V)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    (j : ℝ) (hj : Jump S j)
    (hLawV : MetricJumpClosureLaw dV fV j)
    (x y : A)
    (hRepresentative :
      metricClosureRepresentative fA x =
        metricClosureRepresentative fA y)
    (hExactX : fV (i x) = Option.map i (fA x))
    (hExactY : fV (i y) = Option.map i (fA y)) :
    dV (i x) (i y) ≤ j := by
  apply (metricClosureRepresentative_eq_iff_jump_close
    hpos hS hdV j hj fV hLawV (i x) (i y)).mp
  calc
    metricClosureRepresentative fV (i x) =
        i (metricClosureRepresentative fA x) :=
      metricClosureRepresentative_map_of_exact_value
        i fA fV x hExactX
    _ = i (metricClosureRepresentative fA y) := by
      rw [hRepresentative]
    _ = metricClosureRepresentative fV (i y) :=
      (metricClosureRepresentative_map_of_exact_value
        i fA fV y hExactY).symm

/-- A path of locally tested j-short candidate edges cannot
coexist with a directly specified endpoint edge longer than j
which also passes an exact functional local completion test.

Each short-edge test uses at most four original vertices:
a, b and their two F_j closure representatives. The
completion map MAY DIFFER on every path edge. This result
does not require completion of the whole candidate. -/
theorem metricShortPath_longEdge_localCompletion_obstruction
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {A : Type u} {V : Type v} [LinearOrder V]
    (dA : A → A → ℝ)
    (fA : A → Option A)
    (dV : V → V → ℝ) (fV : V → Option V)
    (hdV : MetricOn S dV)
    (j : ℝ) (hj : Jump S j)
    (hLawV : MetricJumpClosureLaw dV fV j)
    (hLocalEdge :
      ∀ a b : A, dA a b ≤ j →
        ∃ (i : A → V),
          Set.InjOn i
            ({a, b, metricClosureRepresentative fA a,
              metricClosureRepresentative fA b} : Set A) ∧
          dV (i a) (i b) = dA a b ∧
          fV (i a) = Option.map i (fA a) ∧
          fV (i b) = Option.map i (fA b))
    (x y : A)
    (hPath : Relation.ReflTransGen
      (fun a b : A => dA a b ≤ j) x y)
    (hLong : j < dA x y)
    (iLong : A → V)
    (hLongDist : dV (iLong x) (iLong y) = dA x y)
    (hExactX : fV (iLong x) = Option.map iLong (fA x))
    (hExactY : fV (iLong y) = Option.map iLong (fA y)) :
    False := by
  have hEdge :
      ∀ a b : A, dA a b ≤ j →
        metricClosureRepresentative fA a =
          metricClosureRepresentative fA b := by
    intro a b hab
    obtain ⟨i, hInj, hShort, hExactA, hExactB⟩ :=
      hLocalEdge a b hab
    apply metricClosureRepresentative_eq_of_four_point_completion
      hpos i fA fV hdV j hj hLawV a b hInj
    · rw [hShort]
      exact hab
    · exact hExactA
    · exact hExactB
  have hRepresentative :
      metricClosureRepresentative fA x =
        metricClosureRepresentative fA y :=
    metricClosureRepresentative_eq_of_locally_coherent_path
      fA (fun a b : A => dA a b ≤ j) hEdge hPath
  have hShort :
      dV (iLong x) (iLong y) ≤ j :=
    metricClosureRepresentative_jump_close_of_local_endpoint_match
      hpos hS iLong fA fV hdV j hj hLawV
      x y hRepresentative hExactX hExactY
  rw [hLongDist] at hShort
  exact (not_lt_of_ge hShort) hLong

end AllThoseRamseyClasses.Applications.MetricSaturation
