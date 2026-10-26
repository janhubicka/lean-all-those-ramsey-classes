import AllThoseRamseyClasses.Applications.MetricRootedFunctionalDefined

/-!
# Undefined F_j on a common-root vertex controls the whole glued class

If the merged F_j is undefined at a root vertex a, then the
original F_j is undefined at both iU(a) and iV(a) because
the source partial functions agree exactly over the closed root.

The source j-class laws and original-side embeddings therefore
imply that every different glued vertex j-close to a must
precede it, lie at exact distance j, and map to the SAME
common-root vertex under the merged F_j. Crucially, this
covers both private sides of a shared equivalence class.

No all-class or weak local-completion theorem is asserted here;
private root-disjoint classes are checked separately.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v w

/-- An undefined common-root F_j value is the unique designated
last member of its WHOLE glued j-class, with exact function values. -/
theorem metricRootedPartialFunction_none_root_target
    (S : Set ℝ)
    (hpos : Positive S)
    {A : Type u} {U : Type v} {V : Type w}
    [Finite A] [Nonempty A]
    [LinearOrder U] [LinearOrder V]
    (iU : A → U) (iV : A → V)
    (hiU : Function.Injective iU)
    (hiV : Function.Injective iV)
    {dU : U → U → ℝ} {dV : V → V → ℝ}
    (hdU : MetricOn S dU) (hdV : MetricOn S dV)
    (hBase : ∀ a b : A,
      dU (iU a) (iU b) = dV (iV a) (iV b))
    (o : LinearOrder (MetricRootedAmalgamVertex iU iV))
    (hOrderU : ∀ x y : U, x < y →
      @LT.lt _ o.toLT
        (metricRootedLeft iU iV hiU x)
        (metricRootedLeft iU iV hiU y))
    (hOrderV : ∀ x y : V, x < y →
      @LT.lt _ o.toLT
        (metricRootedRight iU iV hiV x)
        (metricRootedRight iU iV hiV y))
    (j : ℝ) (hj : Jump S j)
    (fA : A → Option A)
    (fU : U → Option U) (fV : V → Option V)
    (hExtU : ∀ a : A,
      fU (iU a) = Option.map iU (fA a))
    (hExtV : ∀ a : A,
      fV (iV a) = Option.map iV (fA a))
    (hLawU : MetricJumpClosureLaw dU fU j)
    (hLawV : MetricJumpClosureLaw dV fV j)
    (a : A)
    (hNone : metricRootedPartialFunction
      iU iV hiU hiV fU fV (.inl a) = none)
    (p : MetricRootedAmalgamVertex iU iV)
    (hDifferent : p ≠ .inl a)
    (hClose :
      metricRootedShortestDistance S iU iV dU dV
        p (.inl a) ≤ j) :
    @LT.lt _ o.toLT p (.inl a) ∧
      metricRootedShortestDistance S iU iV dU dV
        p (.inl a) = j ∧
      metricRootedPartialFunction iU iV hiU hiV fU fV
        p = some (.inl a) := by
  have hRoot :=
    metricRootedPartialFunction_root_agree_of_source
      iU iV hiU hiV fA fU fV hExtU hExtV
  have hUNone : fU (iU a) = none := by
    change Option.map (metricRootedLeft iU iV hiU)
      (fU (iU a)) = none at hNone
    cases hf : fU (iU a) with
    | none => simpa [hf]
    | some x => simp [hf] at hNone
  have hVNone : fV (iV a) = none := by
    have hMapped := (hRoot a).symm
    rw [hUNone] at hMapped
    cases hf : fV (iV a) with
    | none => simpa [hf]
    | some x => simp [hf] at hMapped
  rcases metricRooted_covers iU iV hiU hiV p with
    ⟨x, hx⟩ | ⟨z, hz⟩
  · have hXClose : dU x (iU a) ≤ j := by
      have hp := hClose
      rw [← hx, ← metricRootedLeft_root iU iV hiU a,
        metricRootedShortestDistance_left_isometry
          S iU iV hiU dU dV x (iU a)] at hp
      exact hp
    have hXDifferent : x ≠ iU a := by
      intro heq
      have hp : p = (.inl a : MetricRootedAmalgamVertex iU iV) := by
        calc
          p = metricRootedLeft iU iV hiU x := hx.symm
          _ = metricRootedLeft iU iV hiU (iU a) := by rw [heq]
          _ = .inl a := metricRootedLeft_root iU iV hiU a
      exact hDifferent hp
    obtain ⟨hxBefore, hxDist, hxTarget⟩ :=
      metricJumpClosureLaw_none_is_exact_target
        hpos hdU j hj fU hLawU (iU a) hUNone
          x hXDifferent hXClose
    refine ⟨?_, ?_, ?_⟩
    · have h := hOrderU x (iU a) hxBefore
      rw [hx, metricRootedLeft_root] at h
      exact h
    · rw [← hx, ← metricRootedLeft_root iU iV hiU a,
        metricRootedShortestDistance_left_isometry
          S iU iV hiU dU dV x (iU a)]
      exact hxDist
    · rw [← hx, metricRootedPartialFunction_left
        iU iV hiU hiV fU fV x, hxTarget]
      simpa using congrArg Option.some
        (metricRootedLeft_root iU iV hiU a)
  · have hZClose : dV z (iV a) ≤ j := by
      have hp := hClose
      rw [← hz, ← metricRootedRight_root iU iV hiV a,
        metricRootedShortestDistance_right_isometry
          S iU iV hiV dU dV hBase z (iV a)] at hp
      exact hp
    have hZDifferent : z ≠ iV a := by
      intro heq
      have hp : p = (.inl a : MetricRootedAmalgamVertex iU iV) := by
        calc
          p = metricRootedRight iU iV hiV z := hz.symm
          _ = metricRootedRight iU iV hiV (iV a) := by rw [heq]
          _ = .inl a := metricRootedRight_root iU iV hiV a
      exact hDifferent hp
    obtain ⟨hzBefore, hzDist, hzTarget⟩ :=
      metricJumpClosureLaw_none_is_exact_target
        hpos hdV j hj fV hLawV (iV a) hVNone
          z hZDifferent hZClose
    refine ⟨?_, ?_, ?_⟩
    · have h := hOrderV z (iV a) hzBefore
      rw [hz, metricRootedRight_root] at h
      exact h
    · rw [← hz, ← metricRootedRight_root iU iV hiV a,
        metricRootedShortestDistance_right_isometry
          S iU iV hiV dU dV hBase z (iV a)]
      exact hzDist
    · rw [← hz, metricRootedPartialFunction_right
        iU iV hiU hiV fU fV hRoot z, hzTarget]
      simpa using congrArg Option.some
        (metricRootedRight_root iU iV hiV a)

end AllThoseRamseyClasses.Applications.MetricSaturation
