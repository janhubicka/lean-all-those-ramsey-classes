import AllThoseRamseyClasses.Applications.MetricRootedAmalgamVertex

/-!
# Exact common-root intersection of two canonical metric amalgam sides

An amalgamation is STRONG only when original sides are never
accidentally identified away from their prescribed common base.

The identified-base carrier has an exact, source-independent
description of its overlap: a left-side point and a right-side point
agree precisely if BOTH are the same root vertex. Passing through
the side/root equivalences proves the identical assertion for
the genuine original maps U,V into the amalgam.

This is a carrier/embedding fact; no metric triangle, order, or
closure-function statement is silently assumed.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- The two inclusions of the disjoint root/off-root decompositions
intersect at exactly one copy of A, not at any off-root vertices. -/
theorem metricRooted_sideOverlap
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V)
    (p : A ⊕ MetricOutsideRoot iU)
    (q : A ⊕ MetricOutsideRoot iV) :
    metricLeftSideIntoRooted iU iV p =
        metricRightSideIntoRooted iU iV q ↔
      ∃ a : A, p = .inl a ∧ q = .inl a := by
  cases p with
  | inl a =>
      cases q with
      | inl b =>
          constructor
          · intro h
            have hab : a = b := Sum.inl.inj h
            subst b
            exact ⟨a, rfl, rfl⟩
          · rintro ⟨c, ha, hb⟩
            rw [ha, hb]
            rfl
      | inr q =>
          constructor
          · intro h
            cases h
          · rintro ⟨c, _ha, hb⟩
            cases hb
  | inr p =>
      cases q with
      | inl b =>
          constructor
          · intro h
            cases h
          · rintro ⟨c, ha, _hb⟩
            cases ha
      | inr q =>
          constructor
          · intro h
            cases h
          · rintro ⟨c, ha, _hb⟩
            cases ha

/-- The actual canonical embeddings U ↪ W and V ↪ W intersect
exactly on the identified root. This is the non-collapse condition
needed for STRONG metric amalgamation; it does not assert a distance
property of W. -/
theorem metricRooted_sides_intersect_exactly_on_root
    {A : Type u} {U : Type v} {V : Type w}
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (hiV : Function.Injective iV)
    (x : U) (y : V) :
    metricRootedLeft iU iV hiU x =
        metricRootedRight iU iV hiV y ↔
      ∃ a : A, x = iU a ∧ y = iV a := by
  constructor
  · intro h
    let p : A ⊕ MetricOutsideRoot iU :=
      (metricSideEquiv iU hiU).symm x
    let q : A ⊕ MetricOutsideRoot iV :=
      (metricSideEquiv iV hiV).symm y
    have hp : x = metricSideEquiv iU hiU p := by
      dsimp [p]
      exact ((metricSideEquiv iU hiU).apply_symm_apply x).symm
    have hq : y = metricSideEquiv iV hiV q := by
      dsimp [q]
      exact ((metricSideEquiv iV hiV).apply_symm_apply y).symm
    have hsum :
        metricLeftSideIntoRooted iU iV p =
          metricRightSideIntoRooted iU iV q := by
      exact h
    obtain ⟨a, ha, hb⟩ :=
      (metricRooted_sideOverlap iU iV p q).mp hsum
    refine ⟨a, ?_, ?_⟩
    · calc
        x = metricSideEquiv iU hiU p := hp
        _ = iU a := by rw [ha]; rfl
    · calc
        y = metricSideEquiv iV hiV q := hq
        _ = iV a := by rw [hb]; rfl
  · rintro ⟨a, rfl, rfl⟩
    exact metricRooted_sides_agree_on_root iU iV hiU hiV a

end AllThoseRamseyClasses.Applications.MetricSaturation
