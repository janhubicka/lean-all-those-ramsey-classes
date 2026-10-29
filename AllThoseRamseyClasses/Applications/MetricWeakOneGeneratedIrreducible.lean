import AllThoseRamseyClasses.Applications.MetricWeakCandidateFiniteHulls
import Mathlib.Tactic

/-!
# One-generated partial-function closures are irreducible

The repaired 2019 multiamalgamation hypothesis tests all CLOSED
U-irreducible source substructures, not only bounded local pieces.
For unary partial functions there is an elementary reason this may
resolve the weak-candidate small-hull bootstrap:

The least function-closed subset containing one vertex x cannot be
covered by two proper function-closed subsets. If two closed pieces
cover it, one contains x, hence contains the whole generated closure.

This is proved for an arbitrary set A and arbitrary Option-valued
unary maps F_j, with no metric or ambient order assumption.
We then isolate a conditional transfer: if every closed,
join-irreducible piece of a weak candidate satisfies the VALID
two-step F_j composition normal form, so does the entire candidate;
its generated finite seed hulls are consequently bounded by
m (|J|+1), using the independently certified finite-hull lemma.

IMPORTANT: this is NOT a proof that the printed 2019
U-irreducible condition coincides with the join-irreducibility
predicate below. Nor does it certify that arbitrary source
completion maps preserve the exact Option-valued functions.
Those are explicit source-matching requirements. No full
weak local completion, cycle compression or Ramsey conclusion
is inferred without them.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- A set is closed under every specified unary partial F_j
whose value is defined on one of its members. -/
def MetricCandidateSetClosed
    {A : Type u}
    (J : Set ℝ)
    (f : ℝ → A → Option A)
    (C : Set A) : Prop :=
  ∀ j ∈ J, ∀ x ∈ C, ∀ y : A,
    f j x = some y → y ∈ C

/-- Arbitrary unions of two closed subsets are closed because
each F_j has only ONE source vertex. This is not true without
qualification for higher-arity functions. -/
theorem metricCandidateSetClosed_union
    {A : Type u}
    (J : Set ℝ) (f : ℝ → A → Option A)
    (C D : Set A)
    (hC : MetricCandidateSetClosed J f C)
    (hD : MetricCandidateSetClosed J f D) :
    MetricCandidateSetClosed J f (C ∪ D) := by
  intro j hj x hx y hxy
  rcases hx with hxC | hxD
  · exact Or.inl (hC j hj x hxC y hxy)
  · exact Or.inr (hD j hj x hxD y hxy)

/-- The algebraically least function-closed subset containing
one generator x, defined by the intersection of ALL such sets.
No source finiteness or normal-form theorem is assumed. -/
def metricCandidateOneGeneratedClosure
    {A : Type u}
    (J : Set ℝ) (f : ℝ → A → Option A) (x : A) : Set A :=
  {y | ∀ C : Set A,
    x ∈ C → MetricCandidateSetClosed J f C → y ∈ C}

/-- Every generator belongs to its own algebraic closure. -/
theorem metricCandidateOneGeneratedClosure_self
    {A : Type u}
    (J : Set ℝ) (f : ℝ → A → Option A) (x : A) :
    x ∈ metricCandidateOneGeneratedClosure J f x := by
  intro C hx _
  exact hx

/-- The one-generator closure is genuinely function-closed. -/
theorem metricCandidateOneGeneratedClosure_closed
    {A : Type u}
    (J : Set ℝ) (f : ℝ → A → Option A) (x : A) :
    MetricCandidateSetClosed J f
      (metricCandidateOneGeneratedClosure J f x) := by
  intro j hj y hy z hyz C hx hC
  exact hC j hj y (hy C hx hC) z hyz

/-- It is contained in every closed source substructure
containing the generator, by its precise definition. -/
theorem metricCandidateOneGeneratedClosure_minimal
    {A : Type u}
    (J : Set ℝ) (f : ℝ → A → Option A)
    (x : A) (C : Set A)
    (hx : x ∈ C) (hC : MetricCandidateSetClosed J f C) :
    metricCandidateOneGeneratedClosure J f x ⊆ C := by
  intro y hy
  exact hy C hx hC

/-- A closed subset is strongly join-irreducible among the
closed subsets of the ambient functional source: if it is
contained in a union of two closed sets, one of the sets
already contains the whole subset. This is the property
required below, distinct from the specific 2019 U-API. -/
def MetricCandidateClosedJoinIrreducible
    {A : Type u}
    (J : Set ℝ) (f : ℝ → A → Option A)
    (E : Set A) : Prop :=
  ∀ C D : Set A,
    MetricCandidateSetClosed J f C →
    MetricCandidateSetClosed J f D →
    E ⊆ C ∪ D →
      E ⊆ C ∨ E ⊆ D

/-- KEY IRREDUCIBILITY LEMMA: every single-generated
closure is join-irreducible, regardless of the length
or branching of its candidate partial-function orbit.

The proof uses only that at least one of the two closed
sets covering the closure contains its original generator. -/
theorem metricCandidateOneGeneratedClosure_irreducible
    {A : Type u}
    (J : Set ℝ) (f : ℝ → A → Option A) (x : A) :
    MetricCandidateClosedJoinIrreducible J f
      (metricCandidateOneGeneratedClosure J f x) := by
  intro C D hC hD hCover
  have hx : x ∈ C ∪ D :=
    hCover (metricCandidateOneGeneratedClosure_self J f x)
  rcases hx with hxC | hxD
  · exact Or.inl
      (metricCandidateOneGeneratedClosure_minimal
        J f x C hxC hC)
  · exact Or.inr
      (metricCandidateOneGeneratedClosure_minimal
        J f x D hxD hD)

/-- The one-generated closure also contains each defined direct
function value, including every candidate two-step endpoint. -/
theorem metricCandidateOneGeneratedClosure_of_some
    {A : Type u}
    (J : Set ℝ) (f : ℝ → A → Option A)
    (x y : A) (j : ℝ) (hj : j ∈ J)
    (hxy : f j x = some y) :
    y ∈ metricCandidateOneGeneratedClosure J f x := by
  exact metricCandidateOneGeneratedClosure_closed
    J f x j hj x
    (metricCandidateOneGeneratedClosure_self J f x)
    y hxy

/-- Source-wide TWO-STEP normal form follows from validity
of all closed join-irreducible substructures, without any
a priori local hull-size assumption.

The local validity clause explicitly states the normal-form
consequence needed from genuine completed F_j structures;
deriving it from the literal U-irreducible K-test in the
corrected paper is a separate source-matching task. -/
theorem metricCandidateComposition_normalform_of_irreducibles
    {A : Type u}
    (J : Set ℝ)
    (f : ℝ → A → Option A)
    (hValidPieces : ∀ E : Set A,
      MetricCandidateSetClosed J f E →
      MetricCandidateClosedJoinIrreducible J f E →
      ∀ j ∈ J, ∀ k ∈ J,
        ∀ x y z : A,
          x ∈ E → y ∈ E → z ∈ E →
          f j x = some y → f k y = some z →
          j < k ∧ f k x = some z) :
    ∀ j ∈ J, ∀ k ∈ J,
      ∀ x y z : A,
        f j x = some y → f k y = some z →
        j < k ∧ f k x = some z := by
  intro j hj k hk x y z hxy hyz
  let E := metricCandidateOneGeneratedClosure J f x
  have hx : x ∈ E := metricCandidateOneGeneratedClosure_self J f x
  have hy : y ∈ E :=
    metricCandidateOneGeneratedClosure_of_some J f x y j hj hxy
  have hz : z ∈ E :=
    metricCandidateOneGeneratedClosure_closed J f x
      k hk y hy z hyz
  exact hValidPieces E
    (metricCandidateOneGeneratedClosure_closed J f x)
    (metricCandidateOneGeneratedClosure_irreducible J f x)
    j hj k hk x y z hx hy hz hxy hyz

/-- Conditional algebraic consequence:
validity of every one-generated irreducible source piece
produces small closed hulls of all finite seed lists.
This does NOT assume a small closed hull to run a test. -/
theorem metricCandidateFiniteHull_of_irreducibles
    {A : Type u}
    (J : Finset ℝ) (f : ℝ → A → Option A)
    (hValidPieces : ∀ E : Set A,
      MetricCandidateSetClosed (↑J : Set ℝ) f E →
      MetricCandidateClosedJoinIrreducible (↑J : Set ℝ) f E →
      ∀ j ∈ J, ∀ k ∈ J,
        ∀ x y z : A,
          x ∈ E → y ∈ E → z ∈ E →
          f j x = some y → f k y = some z →
          j < k ∧ f k x = some z)
    (seeds : List A) :
    ∃ C : Finset A,
      (∀ x ∈ seeds, x ∈ C) ∧
      C.card ≤ seeds.length * (J.card + 1) ∧
      MetricCandidateFinsetClosed J f C := by
  have hNormal :
      ∀ j ∈ J, ∀ k ∈ J,
        ∀ x y z : A,
          f j x = some y → f k y = some z →
          f k x = some z := by
    intro j hj k hk x y z hxy hyz
    have hV :
        ∀ E : Set A,
          MetricCandidateSetClosed (↑J : Set ℝ) f E →
          MetricCandidateClosedJoinIrreducible (↑J : Set ℝ) f E →
          ∀ j ∈ (↑J : Set ℝ),
          ∀ k ∈ (↑J : Set ℝ),
          ∀ x y z : A,
            x ∈ E → y ∈ E → z ∈ E →
            f j x = some y → f k y = some z →
            j < k ∧ f k x = some z := by
      exact hValidPieces
    exact (metricCandidateComposition_normalform_of_irreducibles
      (↑J : Set ℝ) f hV j hj k hk x y z hxy hyz).2
  exact metricCandidateFiniteHull_list_exists J f hNormal seeds

end AllThoseRamseyClasses.Applications.MetricSaturation
