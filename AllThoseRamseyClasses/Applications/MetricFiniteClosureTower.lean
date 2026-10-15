import AllThoseRamseyClasses.Applications.MetricOnePointClosure

/-!
# Finite towers of genuine metric closure vertices

Iterating the checked one-point jump attachment finitely often
always yields a genuine S-metric, and the original S-metric remains
isometrically embedded. The carrier at stage n is an n-fold nested
Option type; the newest closure vertex is none.

At the i-th step the new vertex is attached at a positive jump
level(i) to the *original* vertex root(i), embedded in the current
tower. The only assumption on levels is positivity/idempotency for
those stages actually used (i<n); n=0 therefore works even when
S has no jumps or is empty.

This is a reusable metric existence theorem for a finite sequence
of closure attachments. It does not yet deduplicate equal jump
classes or construct the canonical ordering of all imaginaries.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- A carrier with n formally distinct new vertices and all original
vertices; at stage n+1 the new vertex is none. -/
def ClosureTower (V : Type u) : ℕ → Type u
  | 0 => V
  | n + 1 => Option (ClosureTower V n)

/-- Embed each original vertex through all n layers of added vertices. -/
def towerOriginal {V : Type u} : (n : ℕ) → V → ClosureTower V n
  | 0, x => x
  | n + 1, x => some (towerOriginal n x)

/-- Iterate the actual one-point metric formula, keeping the roots
in the original vertex set at each step. -/
noncomputable def closureTowerDistance (S : Set ℝ) {V : Type u}
    (d : V → V → ℝ) (roots : ℕ → V) (levels : ℕ → ℝ) :
    (n : ℕ) → ClosureTower V n → ClosureTower V n → ℝ
  | 0 => d
  | n + 1 =>
      onePointDistance S (closureTowerDistance S d roots levels n)
        (towerOriginal n (roots n)) (levels n)

/-- Every finite stage is a genuine S-metric, needing a jump
hypothesis only for the finitely many levels i<n actually attached. -/
theorem closureTowerDistance_metric {S : Set ℝ} {V : Type u}
    (hpos : Positive S) (hS : WellDefined S)
    (hassoc : AssociativeOn S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (roots : ℕ → V) (levels : ℕ → ℝ) :
    ∀ n : ℕ, (∀ i : ℕ, i < n → Jump S (levels i)) →
      MetricOn S (closureTowerDistance S d roots levels n) := by
  intro n
  induction n with
  | zero =>
      intro _
      exact hd
  | succ n ih =>
      intro hlevels
      have hprev : ∀ i : ℕ, i < n → Jump S (levels i) := by
        intro i hi
        exact hlevels i (Nat.lt_trans hi (Nat.lt_succ_self n))
      exact onePointDistance_metric hpos hS hassoc (ih hprev)
        (hlevels n (Nat.lt_succ_self n))
        (towerOriginal n (roots n))

/-- The original metric is preserved exactly at every finite stage,
without assumptions on the attached levels or their order. -/
theorem closureTowerDistance_old (S : Set ℝ) {V : Type u}
    (d : V → V → ℝ) (roots : ℕ → V) (levels : ℕ → ℝ)
    (n : ℕ) (x y : V) :
    closureTowerDistance S d roots levels n
      (towerOriginal n x) (towerOriginal n y) = d x y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change closureTowerDistance S d roots levels n
        (towerOriginal n x) (towerOriginal n y) = d x y
      exact ih

/-- The newest attached closure vertex sees each old original x
at the rounded distance prescribed by its chosen original root. -/
theorem closureTowerDistance_latest_original (S : Set ℝ)
    {V : Type u} (d : V → V → ℝ)
    (roots : ℕ → V) (levels : ℕ → ℝ)
    (n : ℕ) (x : V) :
    closureTowerDistance S d roots levels (n + 1)
      none (towerOriginal (n + 1) x) =
      sumWithZero S (levels n) (d (roots n) x) := by
  change sumWithZero S (levels n)
      (closureTowerDistance S d roots levels n
        (towerOriginal n (roots n)) (towerOriginal n x)) =
    sumWithZero S (levels n) (d (roots n) x)
  rw [closureTowerDistance_old]

/-- The newest vertex has distance at most its jump exactly to
the original class of its root, no more and no less. -/
theorem closureTowerDistance_latest_class_iff {S : Set ℝ}
    {V : Type u} (hpos : Positive S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (roots : ℕ → V) (levels : ℕ → ℝ) (n : ℕ)
    (hj : Jump S (levels n)) (x : V) :
    closureTowerDistance S d roots levels (n + 1)
      none (towerOriginal (n + 1) x) ≤ levels n ↔
      d (roots n) x ≤ levels n := by
  rw [closureTowerDistance_latest_original]
  exact onePointDistance_new_class_iff hpos hd hj (roots n) x

/-- Every original member of the newest jump class is at exactly
the assigned jump distance from the newest closure vertex. -/
theorem closureTowerDistance_latest_to_class {S : Set ℝ}
    {V : Type u} (hpos : Positive S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (roots : ℕ → V) (levels : ℕ → ℝ) (n : ℕ)
    (hj : Jump S (levels n)) (x : V)
    (hx : d (roots n) x ≤ levels n) :
    closureTowerDistance S d roots levels (n + 1)
      none (towerOriginal (n + 1) x) = levels n := by
  rw [closureTowerDistance_latest_original]
  exact onePointDistance_to_class hpos hd hj (roots n) x hx

/-- If the original space is finite, every finite closure tower
still has finitely many vertices (n formal closure points). -/
theorem closureTower_finite {V : Type u} [Finite V] (n : ℕ) :
    Finite (ClosureTower V n) := by
  induction n with
  | zero =>
      change Finite V
      infer_instance
  | succ n ih =>
      letI : Finite (ClosureTower V n) := ih
      change Finite (Option (ClosureTower V n))
      infer_instance

end AllThoseRamseyClasses.Applications.MetricSaturation
