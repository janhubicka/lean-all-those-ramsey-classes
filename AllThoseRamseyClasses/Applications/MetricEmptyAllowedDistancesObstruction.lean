import AllThoseRamseyClasses.Applications.MetricEmptyBaseAmalgamation

/-!
# Empty allowed distance set: exact strong-amalgamation endpoint

If S is empty, every S-metric has at most one point: two distinct
points would need a positive off-diagonal distance from the empty
set. Thus two independent one-point S-metrics cannot both embed
with disjoint images into a third S-metric over the empty root.

This is an exact *strong amalgamation* obstruction to leaving
S possibly empty in the printed auxiliary metric class theorem.
It is NOT a counterexample to the Ramsey property: the class of
finite S-metrics with at most one point has a trivial Ramsey theory.

The separate verified nonempty-S empty-root construction glues
two metric spaces by assigning each cross edge max(S).
There is no such maximum when S is empty.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Every genuine metric with no allowed positive distances has
at most one vertex, without making any finiteness assumption. -/
theorem metric_empty_allowed_distances_subsingleton
    {V : Type u} (d : V → V → ℝ)
    (hd : MetricOn (∅ : Set ℝ) d) :
    Subsingleton V := by
  refine ⟨?_⟩
  intro x y
  by_contra hne
  have hFalse : d x y ∈ (∅ : Set ℝ) := hd.values x y hne
  simpa using hFalse

/-- A two-point carrier cannot be an S-metric when S is empty.
In particular, two independent singleton metrics cannot have
a STRONG amalgam over the empty root under this language. -/
theorem metric_empty_allowed_distances_no_two_vertices
    (d : Bool → Bool → ℝ) :
    ¬ MetricOn (∅ : Set ℝ) d := by
  intro hd
  have hFalse : d false true ∈ (∅ : Set ℝ) :=
    hd.values false true (by decide)
  simpa using hFalse

end AllThoseRamseyClasses.Applications.MetricSaturation
