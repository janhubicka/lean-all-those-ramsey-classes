import AllThoseRamseyClasses.Applications.MetricFunctionalJumpClosureLaw

/-!
# A bounded metric edge forces one common designated closure

The printed 2019 proof of local metric completion says that a
path whose edges lie below one proper jump threshold has a
COMMON F_j closure vertex. This module isolates the exact
edge-level fact behind that assertion.

For a genuine metric source satisfying the LITERAL partial
F_j class law, define the closure representative of x as
F_j(x) when that value is defined, and as x when F_j(x)
is undefined. Two j-close vertices have the SAME representative,
because they lie in the same class with one designated last point.

More importantly, this equality pulls BACK through an injective
map into a valid completion if the two endpoint partial-function
values are preserved exactly, including undefinedness. Hence a
single short candidate edge and a local completion of its
functional data already force agreement of the original closure
representatives. No global metric completion of the candidate
is needed for this *local* inference.

The next separate step is to propagate this forced equality
along arbitrary j-short paths and account for the exact finite
weak-substructure size bound. We do not assert that the
published local-completion lemma or its cycle bound is proved.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- The designated closure of x according to the actual
Option-valued partial function, including undefined values. -/
def metricClosureRepresentative
    {V : Type u} (f : V → Option V) (x : V) : V :=
  (f x).getD x

/-- A complete source satisfying the printed F_j law sends
j-close vertices to precisely the SAME designated closure.
No arbitrary selection of equivalent representatives occurs. -/
theorem metricClosureRepresentative_eq_of_close
    {S : Set ℝ}
    (hpos : Positive S)
    {V : Type u} [LinearOrder V]
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j)
    (f : V → Option V)
    (hLaw : MetricJumpClosureLaw d f j)
    (x y : V) (hxy : d x y ≤ j) :
    metricClosureRepresentative f x =
      metricClosureRepresentative f y := by
  obtain ⟨c, _hxc, hcNone, hClass⟩ := hLaw x
  have hxx : d x x ≤ j := by
    rw [hd.diag x]
    exact (hpos j hj.1).le
  have hyx : d y x ≤ j := by
    rw [hd.symm y x]
    exact hxy
  have hxRep : metricClosureRepresentative f x = c := by
    rcases hClass x hxx with hx | ⟨_, _, hf⟩
    · subst x
      simp [metricClosureRepresentative, hcNone]
    · simp [metricClosureRepresentative, hf]
  have hyRep : metricClosureRepresentative f y = c := by
    rcases hClass y hyx with hy | ⟨_, _, hf⟩
    · subst y
      simp [metricClosureRepresentative, hcNone]
    · simp [metricClosureRepresentative, hf]
  exact hxRep.trans hyRep.symm

/-- If one partial-function value is preserved EXACTLY by
a map, then its associated closure representative is
preserved as well, even if the value is undefined. -/
theorem metricClosureRepresentative_map_of_exact_value
    {A : Type u} {V : Type v}
    (i : A → V)
    (fA : A → Option A) (fV : V → Option V)
    (x : A)
    (hExact : fV (i x) = Option.map i (fA x)) :
    metricClosureRepresentative fV (i x) =
      i (metricClosureRepresentative fA x) := by
  unfold metricClosureRepresentative
  rw [hExact]
  cases hx : fA x with
  | none => simp [hx]
  | some y => simp [hx]

/-- A LOCAL genuine metric completion of two candidate endpoints
forces equality of their OLD closure representatives. It suffices
to preserve the Option function on those endpoints, not on the
whole source. This covers undefined values without an implicit
domain enlargement or arbitrary closure choice. -/
theorem metricClosureRepresentative_eq_of_local_completion
    {S : Set ℝ}
    (hpos : Positive S)
    {A : Type u} {V : Type v} [LinearOrder V]
    (i : A → V) (hi : Function.Injective i)
    (fA : A → Option A) (fV : V → Option V)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    (j : ℝ) (hj : Jump S j)
    (hLawV : MetricJumpClosureLaw dV fV j)
    (x y : A)
    (hShort : dV (i x) (i y) ≤ j)
    (hExactX : fV (i x) = Option.map i (fA x))
    (hExactY : fV (i y) = Option.map i (fA y)) :
    metricClosureRepresentative fA x =
      metricClosureRepresentative fA y := by
  apply hi
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

end AllThoseRamseyClasses.Applications.MetricSaturation
