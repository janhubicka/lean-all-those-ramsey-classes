import AllThoseRamseyClasses.Applications.MetricLocalShortPathLongEdgeObstruction

/-!
# Local short-path obstruction with different completion targets per edge

The 2019 S-metric Ramsey proof considers completions of bounded
WEAK INDUCED source subsets. There is no reason to require all
local tests to embed into the same target structure, or even to
share a common target type.

We express a four-point local test as a Prop-valued predicate.
Its witness may choose a completely new ordered S-metric V, its
Option-valued partial F_j law, and its map from the candidate
for EACH separately tested pair (a,b). Only the images of the
two endpoints and their candidate F_j representatives need to
be injective, and only the one original pair distance and
the two exact partial-function values must be preserved.

From the existence of one such test at every j-short source
edge, the OLD F_j closure representatives are equal along
every finite j-short source walk. A further independently
chosen four-point test at a closing source edge of length
strictly greater than j is then IMPOSSIBLE.

This eliminates a global target hypothesis of the earlier
test and isolates a sharp quantitative obstruction. It does
not yet derive the four-point tests from the literal weak
induced-substructure completion axiom, nor the printed
nonmetric-cycle reduction and uniform cutoff.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- A local candidate test at (a,b) may choose ANY valid
ordered target S-metric and map. Its injectivity, distance,
and exact Option-F_j preservation are demanded only on the
explicit four-vertex candidate support. -/
def MetricFourPointFunctionalLocalTest
    (S : Set ℝ) {A : Type u}
    (dA : A → A → ℝ) (fA : A → Option A)
    (j : ℝ) (a b : A) : Prop :=
  ∃ (V : Type u) (o : LinearOrder V)
    (dV : V → V → ℝ) (fV : V → Option V)
    (i : A → V),
    MetricOn S dV ∧
    @MetricJumpClosureLaw V o dV fV j ∧
    Set.InjOn i
      ({a, b, metricClosureRepresentative fA a,
        metricClosureRepresentative fA b} : Set A) ∧
    dV (i a) (i b) = dA a b ∧
    fV (i a) = Option.map i (fA a) ∧
    fV (i b) = Option.map i (fA b)

/-- Even if every short edge chooses a completely DIFFERENT
valid completion target, its four-point test forces equality
of the original designated closure representatives. -/
theorem metricClosureRepresentative_eq_of_varying_fourPointTests
    {S : Set ℝ}
    (hpos : Positive S)
    {A : Type u}
    (dA : A → A → ℝ) (fA : A → Option A)
    (j : ℝ) (hj : Jump S j)
    (hLocal : ∀ a b : A, dA a b ≤ j →
      MetricFourPointFunctionalLocalTest S dA fA j a b)
    {x y : A}
    (hPath : Relation.ReflTransGen
      (fun a b : A => dA a b ≤ j) x y) :
    metricClosureRepresentative fA x =
      metricClosureRepresentative fA y := by
  apply metricClosureRepresentative_eq_of_locally_coherent_path
    fA (fun a b : A => dA a b ≤ j)
  · intro a b hab
    obtain ⟨V, o, dV, fV, i, hdV, hLaw, hInj,
      hDist, hExactA, hExactB⟩ := hLocal a b hab
    letI : LinearOrder V := o
    apply metricClosureRepresentative_eq_of_four_point_completion
      hpos i fA fV hdV j hj hLaw a b hInj
    · rw [hDist]
      exact hab
    · exact hExactA
    · exact hExactB
  · exact hPath

/-- A path of short source edges plus a directly prescribed
long closing edge is incompatible with all four-point local
functional completion tests, even with VARIABLE target types.

The only source hypotheses are a prescribed real edge length
function, an Option-valued partial F_j table, a j-short walk,
and locally available completion witnesses. No global
candidate metric, embedding, or closure of the candidate is
assumed. -/
theorem metricShortPath_longEdge_obstruction_of_varying_fourPointTests
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {A : Type u}
    (dA : A → A → ℝ) (fA : A → Option A)
    (j : ℝ) (hj : Jump S j)
    (hLocal : ∀ a b : A, dA a b ≤ j →
      MetricFourPointFunctionalLocalTest S dA fA j a b)
    (x y : A)
    (hPath : Relation.ReflTransGen
      (fun a b : A => dA a b ≤ j) x y)
    (hLong : j < dA x y)
    (hClosingTest : MetricFourPointFunctionalLocalTest
      S dA fA j x y) :
    False := by
  have hRep : metricClosureRepresentative fA x =
      metricClosureRepresentative fA y :=
    metricClosureRepresentative_eq_of_varying_fourPointTests
      hpos dA fA j hj hLocal hPath
  obtain ⟨V, o, dV, fV, i, hdV, hLaw, _hInj,
    hDist, hExactX, hExactY⟩ := hClosingTest
  letI : LinearOrder V := o
  have hNear : dV (i x) (i y) ≤ j :=
    metricClosureRepresentative_jump_close_of_local_endpoint_match
      hpos hS i fA fV hdV j hj hLaw x y
      hRep hExactX hExactY
  rw [hDist] at hNear
  exact (not_lt_of_ge hNear) hLong

end AllThoseRamseyClasses.Applications.MetricSaturation
