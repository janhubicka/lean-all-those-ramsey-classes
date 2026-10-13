import AllThoseRamseyClasses.Published.InducedClosed2019UnrestrictedInitial
import Mathlib.Tactic

/-!
# Elementary application certificates: ordered posets and nonmetric cycles

This module checks the precise finite counting implications used by
the non-lift applications of the 2019 paper, after correcting the
target-class premise in the poset argument and the edge count in the
no-jumps S-metric-cycle argument.

These proofs are intentionally not declarations of the full application
Ramsey properties. In particular, the poset module does not assert
that its required homomorphism-embedding is automatically strict on
all vertices; the checked strictness is on the selected quasi-cycle
edges. The metric module assumes monotonicity of the iterated S-sum.
-/


namespace AllThoseRamseyClasses.Applications

universe v

/-- A selected witness path of n+1 vertices maps strictly increasingly
along each consecutive edge into a finite linear order; consequently
all its images are distinct and its size is bounded by the control.
This is the numeric step of the quasi-cycle argument. -/
theorem quasiCycle_control_card_bound
    {D : Type v} [LinearOrder D] [Fintype D]
    {n : ℕ}
    (imagePath : Fin (n + 1) → D)
    (hNext : ∀ i : Fin n,
      imagePath i.castSucc < imagePath i.succ) :
    n + 1 ≤ Fintype.card D := by
  have hmono : StrictMono imagePath :=
    (Fin.strictMono_iff_lt_succ).2 hNext
  have hcard := Fintype.card_le_of_injective imagePath hmono.injective
  simpa using hcard

/-- If the iterated positive S-sum of m is monotone and n copies
already reach M, an offending cycle with k vertices whose other
k-1 edges have S-length strictly below M must have k<=n.
There is NO incorrect k*m estimate or m<n conclusion. -/
theorem nonmetric_cycle_card_bound
    {S : Type v} [Preorder S]
    (times : ℕ → S) (htimes : Monotone times)
    (M : S) (n k : ℕ)
    (hReach : M ≤ times n)
    (hShort : times (k - 1) < M) :
    k ≤ n := by
  by_contra h
  have hle : n ≤ k - 1 := by omega
  have hmon := htimes hle
  exact (not_lt_of_ge (hReach.trans hmon)) hShort

end AllThoseRamseyClasses.Applications
