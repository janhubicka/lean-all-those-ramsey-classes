import AllThoseRamseyClasses.Applications.MetricFiniteClosureTower
import AllThoseRamseyClasses.Applications.MetricJumpQuotient

/-!
# Indexed metric closure vertices and every pairwise cross-distance

The finite tower metric is already checked. We now index each
distinctly attached closure vertex by its stage i<n and prove an
explicit formula for all of its distances to original vertices
and to every *other* closure vertex.

For i ≠ k:

  d_tower(v_i, v_k) = levels(i) ⊕ d(roots(i),roots(k)) ⊕ levels(k).

This is the quotient-invariant sandwich label and does not
depend on other attachments between i and k, or their order.
The proof is induction on the number of vertices, with the
one-point preservation theorem discharging old-old cases.

No quotient identification is performed: if two stages use
the same level and class, these are still two distinct tags.
The canonical lift must select one representative of each
(level,class) before applying this tower.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- The vertex introduced at index i<n, transported through all
later Option layers. -/
def towerClosure {V : Type u} : (n i : ℕ) → i < n → ClosureTower V n
  | 0, i, hi => by omega
  | n + 1, i, hi =>
      if h : i = n then none
      else some (towerClosure n i (by omega))

@[simp] theorem towerClosure_succ_last {V : Type u} (n : ℕ) :
    towerClosure (V := V) (n + 1) n (by omega) = none := by
  simp [towerClosure]
  rfl

@[simp] theorem towerClosure_succ_old {V : Type u} (n i : ℕ)
    (hi : i < n) :
    towerClosure (V := V) (n + 1) i (Nat.lt_succ_of_lt hi) =
      some (towerClosure n i hi) := by
  simp [towerClosure, Nat.ne_of_lt hi]
  rfl

/-- Each indexed closure representative has its prescribed rounded
distance to every original vertex, independently of all subsequent
attachments. This theorem does not need any jump assumptions. -/
theorem closureTowerDistance_closure_original (S : Set ℝ)
    {V : Type u} (d : V → V → ℝ)
    (roots : ℕ → V) (levels : ℕ → ℝ) :
    ∀ n i (hi : i < n) (x : V),
      closureTowerDistance S d roots levels n
        (towerClosure n i hi) (towerOriginal n x) =
      sumWithZero S (levels i) (d (roots i) x) := by
  intro n
  induction n with
  | zero =>
      intro i hi x
      omega
  | succ n ih =>
      intro i hi x
      by_cases hlast : i = n
      · subst i
        simpa only [towerClosure_succ_last] using
          (closureTowerDistance_latest_original S d roots levels n x)
      · have hprev : i < n := by omega
        calc
          closureTowerDistance S d roots levels (n + 1)
              (towerClosure (n + 1) i hi) (towerOriginal (n + 1) x) =
            closureTowerDistance S d roots levels n
              (towerClosure n i hprev) (towerOriginal n x) := by
                simp [towerClosure, hlast, closureTowerDistance,
                  towerOriginal, onePointDistance]
          _ = sumWithZero S (levels i) (d (roots i) x) :=
            ih i hprev x

/-- A finite metric tower carries the same explicit sandwich
distance between any two distinct closure vertices, regardless of
their indices or the other vertices inserted along the way. -/
theorem closureTowerDistance_twoClosures {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (roots : ℕ → V) (levels : ℕ → ℝ) :
    ∀ n : ℕ, (∀ i, i < n → Jump S (levels i)) →
      ∀ i k (hi : i < n) (hk : k < n), i ≠ k →
        closureTowerDistance S d roots levels n
          (towerClosure n i hi) (towerClosure n k hk) =
        sumWithZero S
          (sumWithZero S (levels i) (d (roots i) (roots k)))
          (levels k) := by
  intro n
  induction n with
  | zero =>
      intro _ i k hi hk hne
      omega
  | succ n ih =>
      intro hlevels i k hi hk hne
      have hprev : ∀ x, x < n → Jump S (levels x) := by
        intro x hx
        exact hlevels x (by omega)
      by_cases hilast : i = n
      · subst i
        have hkprev : k < n := by omega
        have hmetric : MetricOn S
            (closureTowerDistance S d roots levels n) :=
          closureTowerDistance_metric hpos hS hassoc hd roots levels n hprev
        calc
          closureTowerDistance S d roots levels (n + 1)
              (towerClosure (n + 1) n hi) (towerClosure (n + 1) k hk) =
            sumWithZero S (levels n)
              (closureTowerDistance S d roots levels n
                (towerOriginal n (roots n))
                (towerClosure n k hkprev)) := by
                  simp [towerClosure, Nat.ne_of_lt hkprev,
                    closureTowerDistance, onePointDistance]
          _ = sumWithZero S (levels n)
                (closureTowerDistance S d roots levels n
                  (towerClosure n k hkprev) (towerOriginal n (roots n))) := by
                    rw [hmetric.symm]
          _ = sumWithZero S (levels n)
                (sumWithZero S (levels k) (d (roots k) (roots n))) := by
                    rw [closureTowerDistance_closure_original]
          _ = sumWithZero S
                (sumWithZero S (levels n) (d (roots n) (roots k)))
                (levels k) := by
                    rw [hd.symm (roots k) (roots n)]
                    rw [sumWithZero_comm S (levels k) (d (roots n) (roots k))]
                    exact (sumWithZero_assoc hpos hS hassoc
                      (Or.inr (hlevels n (by omega)).1)
                      (metric_value_mem hd (roots n) (roots k))
                      (Or.inr (hprev k hkprev).1)).symm
      · have hiprev : i < n := by omega
        by_cases hklast : k = n
        · subst k
          calc
            closureTowerDistance S d roots levels (n + 1)
                (towerClosure (n + 1) i hi)
                (towerClosure (n + 1) n hk) =
              sumWithZero S
                (closureTowerDistance S d roots levels n
                  (towerClosure n i hiprev)
                  (towerOriginal n (roots n))) (levels n) := by
                    simp [towerClosure, hilast, closureTowerDistance,
                      onePointDistance]
            _ = sumWithZero S
                  (sumWithZero S (levels i) (d (roots i) (roots n)))
                  (levels n) := by
                    rw [closureTowerDistance_closure_original]
        · have hkprev : k < n := by omega
          calc
            closureTowerDistance S d roots levels (n + 1)
                (towerClosure (n + 1) i hi) (towerClosure (n + 1) k hk) =
              closureTowerDistance S d roots levels n
                (towerClosure n i hiprev) (towerClosure n k hkprev) := by
                  simp [towerClosure, hilast, hklast, closureTowerDistance,
                    onePointDistance]
            _ = sumWithZero S
                  (sumWithZero S (levels i) (d (roots i) (roots k)))
                  (levels k) := ih hprev i k hiprev hkprev hne

end AllThoseRamseyClasses.Applications.MetricSaturation
