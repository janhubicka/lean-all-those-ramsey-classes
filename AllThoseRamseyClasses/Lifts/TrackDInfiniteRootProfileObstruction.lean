import AllThoseRamseyClasses.Lifts.TrackDProtectedHalvesObstruction
import Mathlib.Tactic

/-!
# Track D: unbounded incompatible contexts exclude any finite root code

The merged TrackDProtectedHalvesObstruction theorem proves a
2^r cardinal lower bound whenever there are 2^r pairwise
nonamalgamable ORIGINAL rooted contexts and equal expanded
root profiles imply an allowed amalgam.

This module discharges the final *numeric* infinite step:
NO FINITE profile type can satisfy all these finite lower
bounds at once. The proof is a plain diagonal at
r = Fintype.card Profile.

It does NOT infer the existence of 2^r incompatible contexts
from the proposed Gamma_m family, and it does NOT manufacture
an expansion property. Those remain separate concrete source
and age-compatibility proof obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The elementary strict growth estimate used for the infinite
profile lower bound, with no asymptotic argument or choice. -/
theorem nat_lt_two_pow_self (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero =>
      decide
  | succ n ih =>
      have hPositive : 0 < 2 ^ n := pow_pos (by decide : 0 < (2 : ℕ)) _
      have hBound : n + 1 ≤ 2 ^ n := Nat.succ_le_iff.mpr ih
      rw [pow_succ]
      omega

/-- A family of pairwise nonamalgamable 2^r original rooted contexts
for EVERY finite r forces the profile type to be infinite, whenever
coincident root profiles imply an allowed rooted amalgam.

This is the abstract no-precompactness conclusion. It is valid
for arbitrary native relation/function signatures and an infinite
forbidden family, because the only finite objects counted are
the proposed root profiles and the finite Fin(2^r) index types. -/
theorem impossibleFiniteRootProfiles_of_unboundedNonamalgamableContexts
    (F : ∀ {W : Type}, Structure L W → Prop)
    {Profile VX : Type}
    [Fintype Profile]
    (X : Structure L VX)
    (hContexts : ∀ r : ℕ,
      ∃ (VA : Type)
        (A : Fin (2 ^ r) → Structure L VA)
        (iA : ∀ i : Fin (2 ^ r), Structure.Embedding X (A i))
        (profile : Fin (2 ^ r) → Profile),
        (∀ i j : Fin (2 ^ r), i ≠ j →
          ¬ HasAllowedRootedAmalgam F X
            (A i) (A j) (iA i) (iA j)) ∧
        (∀ i j : Fin (2 ^ r), profile i = profile j →
          HasAllowedRootedAmalgam F X
            (A i) (A j) (iA i) (iA j))) :
    False := by
  let n := Fintype.card Profile
  obtain ⟨VA, A, iA, profile, hNo, hSame⟩ := hContexts n
  have hBound : 2 ^ n ≤ Fintype.card Profile :=
    twoPow_le_card_rootProfiles_of_nonamalgamable
      F n X A iA profile hNo hSame
  have hStrict : Fintype.card Profile < 2 ^ n := by
    simpa only [n] using (nat_lt_two_pow_self n)
  exact (Nat.not_le_of_gt hStrict) hBound

end AllThoseRamseyClasses.Lifts
