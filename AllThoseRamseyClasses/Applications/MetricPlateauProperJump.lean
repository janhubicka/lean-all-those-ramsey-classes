import AllThoseRamseyClasses.Applications.MetricJumpThresholds
import Mathlib.Tactic

/-!
# A genuine unimportant prefix plateau forces a proper jump

An important step of the printed `lem:Sequivalence` is the assertion
that every unimportant path (a constant rounded-prefix segment below
the incompatible closing edge) can be assigned a proper jump at least
as large as each of its positive edge lengths.

The scalar mechanism does NOT need finiteness of S. Let
a,b,d ∈ S, with a<d and a⊕b=a. Positive powers of b capped at d
stabilize (the previously verified power-stabilization theorem).
Associativity and absorption show every capped power of b is
already ≤a, so capping is never active on those powers. At the
stable value j, the positive-power product formula gives
j⊕j=j, while b≤j≤a<d. Hence j is a GENUINE proper jump.

The resulting theorem closes the existence-of-a-jump part of
the unimportant-path argument once each original edge is
known to be absorbed by the constant prefix. It does NOT yet
identify the MAXIMUM of the paper's no-jump block as an absorbed
threshold, nor verify arbitrary replacement paths or the
full cycle-compression and metric Ramsey proof.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- The product of two capped positive powers is the power
indexed by the sum of their positive exponents. The proof uses
genuine capped associativity, not a free semigroup axiom. -/
theorem cappedPositivePower_product
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d b : ℝ} (hd : d ∈ S) (hb : b ∈ S)
    (hbd : b ≤ d) (n k : ℕ) :
    cappedSum S d (power S d b n) (power S d b k) =
      power S d b (n + k + 1) := by
  induction k with
  | zero =>
      change cappedSum S d (power S d b n) b =
        power S d b (n + 1)
      rfl
  | succ k ih =>
      have hn := (power_mem_le hS hd hb hbd n).1
      have hk := (power_mem_le hS hd hb hbd k).1
      calc
        cappedSum S d (power S d b n) (power S d b (k + 1)) =
            cappedSum S d (power S d b n)
              (cappedSum S d (power S d b k) b) := rfl
        _ = cappedSum S d
              (cappedSum S d (power S d b n) (power S d b k)) b :=
            (cappedSum_assoc hpos hS hassoc hd hn hk hb).symm
        _ = cappedSum S d (power S d b (n + k + 1)) b := by rw [ih]
        _ = power S d b (n + (k + 1) + 1) := by
          have heq : n + (k + 1) + 1 = (n + k + 1) + 1 := by omega
          rw [heq]
          rfl

/-- If an allowed prefix a absorbs a positive edge b while
there is still a larger allowed closing distance d, the
rounded distance algebra HAS a proper jump j absorbing b's
stable powers: b≤j≤a<d.

No S-finiteness, maximum choice, or a priori block partition
is assumed; only the manuscript's well-defined associative
rounded operation and positivity. -/
theorem roundedPlateau_has_properJump
    {S : Set ℝ} (hpos : Positive S)
    (hS : WellDefined S) (hassoc : AssociativeOn S)
    {a b d : ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hd : d ∈ S)
    (had : a < d) (hAbs : distanceSum S a b = a) :
    ∃ j : ℝ, Jump S j ∧ b ≤ j ∧ j ≤ a := by
  have hb_le_a : b ≤ a := by
    calc
      b ≤ distanceSum S b a :=
        left_le_distanceSum hb (hpos a ha).le
      _ = distanceSum S a b := distanceSum_comm S b a
      _ = a := hAbs
  have hbd : b ≤ d := hb_le_a.trans (le_of_lt had)
  have hAbsP : ∀ n : ℕ, distanceSum S a (power S d b n) = a := by
    intro n
    induction n with
    | zero => exact hAbs
    | succ n ih =>
        have hp : power S d b n ∈ S :=
          (power_mem_le hS hd hb hbd n).1
        have hr : distanceSum S (power S d b n) b ∈ S :=
          hS _ hp _ hb
        have hAbsRaw :
            distanceSum S a (distanceSum S (power S d b n) b) = a := by
          calc
            distanceSum S a (distanceSum S (power S d b n) b) =
                distanceSum S (distanceSum S a (power S d b n)) b :=
              (hassoc a ha (power S d b n) hp b hb).symm
            _ = distanceSum S a b := by rw [ih]
            _ = a := hAbs
        have hRawLe :
            distanceSum S (power S d b n) b ≤ d := by
          calc
            distanceSum S (power S d b n) b ≤
                distanceSum S (distanceSum S (power S d b n) b) a :=
              left_le_distanceSum hr (hpos a ha).le
            _ = distanceSum S a (distanceSum S (power S d b n) b) :=
              distanceSum_comm S _ _
            _ = a := hAbsRaw
            _ ≤ d := le_of_lt had
        have hCap :
            cappedSum S d (power S d b n) b =
              distanceSum S (power S d b n) b := by
          exact min_eq_right hRawLe
        calc
          distanceSum S a (power S d b (n + 1)) =
              distanceSum S a (distanceSum S (power S d b n) b) := by
            change distanceSum S a (cappedSum S d (power S d b n) b) = _
            rw [hCap]
          _ = a := hAbsRaw
  have hPowLe : ∀ n : ℕ, power S d b n ≤ a := by
    intro n
    have hp : power S d b n ∈ S :=
      (power_mem_le hS hd hb hbd n).1
    calc
      power S d b n ≤ distanceSum S (power S d b n) a :=
        left_le_distanceSum hp (hpos a ha).le
      _ = distanceSum S a (power S d b n) :=
        distanceSum_comm S _ _
      _ = a := hAbsP n
  have hbPow : ∀ n : ℕ, b ≤ power S d b n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        exact ih.trans (power_le_succ hS hd hb (hpos b hb) hbd n)
  obtain ⟨N, hN⟩ := exists_power_stable
    hS hd hb (hpos b hb) hbd
  let j : ℝ := power S d b N
  have hjS : j ∈ S := (power_mem_le hS hd hb hbd N).1
  have hjLe : j ≤ a := hPowLe N
  have hjAbs : distanceSum S a j = a := hAbsP N
  have hjjS : distanceSum S j j ∈ S := hS j hjS j hjS
  have hAbsDouble : distanceSum S a (distanceSum S j j) = a := by
    calc
      distanceSum S a (distanceSum S j j) =
          distanceSum S (distanceSum S a j) j :=
        (hassoc a ha j hjS j hjS).symm
      _ = distanceSum S a j := by rw [hjAbs]
      _ = a := hjAbs
  have hjjLe : distanceSum S j j ≤ d := by
    calc
      distanceSum S j j ≤ distanceSum S (distanceSum S j j) a :=
        left_le_distanceSum hjjS (hpos a ha).le
      _ = distanceSum S a (distanceSum S j j) :=
        distanceSum_comm S _ _
      _ = a := hAbsDouble
      _ ≤ d := le_of_lt had
  have hCapJJ : cappedSum S d j j = distanceSum S j j := by
    exact min_eq_right hjjLe
  have hStableTail : power S d b (N + N + 1) = j := by
    have h := power_eq_of_stable hN (N + 1)
    simpa only [Nat.add_assoc, j] using h
  have hjIdem : distanceSum S j j = j := by
    calc
      distanceSum S j j = cappedSum S d j j := hCapJJ.symm
      _ = power S d b (N + N + 1) :=
        cappedPositivePower_product hpos hS hassoc hd hb hbd N N
      _ = j := hStableTail
  exact ⟨j, ⟨hjS, ⟨d, hd, lt_of_le_of_lt hjLe had⟩, hjIdem⟩,
    hbPow N, hjLe⟩

/-- Specialize to the actual four-values premise of the manuscript. -/
theorem roundedPlateau_has_properJump_of_fourValues
    {S : Set ℝ} (hpos : Positive S)
    (hS : WellDefined S) (h4 : FourValues S)
    {a b d : ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hd : d ∈ S)
    (had : a < d) (hAbs : distanceSum S a b = a) :
    ∃ j : ℝ, Jump S j ∧ b ≤ j ∧ j ≤ a :=
  roundedPlateau_has_properJump hpos hS
    (associativeOn_of_fourValues hpos hS h4)
    ha hb hd had hAbs

end AllThoseRamseyClasses.Applications.MetricSaturation
