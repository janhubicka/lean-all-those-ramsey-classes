import AllThoseRamseyClasses.Applications.MetricLocalClosureCoherence
import Mathlib.Logic.Relation

/-!
# Propagate locally forced F_j closure values along weak short paths

The published local-completion proof of the S-metric Ramsey
application uses "unimportant" short paths and asserts a
COMMON F_j closure vertex for each such path.

A single j-short edge has an exact coherent closure
representative in every valid target, and this is forced
back into a weak candidate by an injective Option-preserving
local completion. This file proves the independent propagation
step: any finite chain of short candidate edges whose endpoint
closure representatives agree must carry one common
representative across the whole connected chain.

We use Relation.ReflTransGen, explicitly allowing a path of
length zero, so no arbitrary fixed path-length bound or
assumption of simple vertices is introduced.

This is a genuine local-to-path proof ingredient, but it
does not prove that all the relevant edges satisfy the
local test hypothesis under the ORIGINAL weak induced-subset
definition or the printed size bound. Nor does it assert
a completion of the whole candidate or a Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Equality of closure representatives propagates along
an arbitrary finite chain of locally certified edges,
regardless of repeated vertices or path length. -/
theorem metricClosureRepresentative_eq_of_locally_coherent_path
    {A : Type u}
    (f : A → Option A)
    (E : A → A → Prop)
    (hEdge : ∀ x y : A, E x y →
      metricClosureRepresentative f x =
        metricClosureRepresentative f y)
    {x y : A}
    (hPath : Relation.ReflTransGen E x y) :
    metricClosureRepresentative f x =
      metricClosureRepresentative f y := by
  induction hPath with
  | refl => rfl
  | tail _ hxy ih =>
      exact ih.trans (hEdge _ _ hxy)

/-- In a VALID S-metric F_j source, every pair linked by
a finite walk of j-short edges has the same closure value.
No assumption that the edge relation is itself transitive
or that the walk is an induced path is needed. -/
theorem metricClosureRepresentative_eq_of_metric_short_walk
    {S : Set ℝ}
    (hpos : Positive S)
    {V : Type u} [LinearOrder V]
    {d : V → V → ℝ} (hd : MetricOn S d)
    (j : ℝ) (hj : Jump S j)
    (f : V → Option V)
    (hLaw : MetricJumpClosureLaw d f j)
    {x y : V}
    (hPath : Relation.ReflTransGen (fun a b : V => d a b ≤ j) x y) :
    metricClosureRepresentative f x =
      metricClosureRepresentative f y := by
  apply metricClosureRepresentative_eq_of_locally_coherent_path
    f (fun a b : V => d a b ≤ j)
  · intro a b hab
    exact metricClosureRepresentative_eq_of_close
      hpos hd j hj f hLaw a b hab
  · exact hPath

end AllThoseRamseyClasses.Applications.MetricSaturation
