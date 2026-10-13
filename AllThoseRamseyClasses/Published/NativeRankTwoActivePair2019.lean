import AllThoseRamseyClasses.Published.NativePositiveGeneratorIndices2019
import Mathlib.Tactic

/-!
# Intrinsic U-rank TWO native weak histories: only ONE transverse pair

The corrected 2019 finite native source may map NONINJECTIVELY to a
genuine simultaneous Hales--Jewett attachment. The verified positive
generator theorem bounds the number of distinct PRIVATE-active copy
indices by the intrinsic U-generating rank of the ORIGINAL weak source.

At intrinsic rank <=2, there are at most TWO active lines. If they
have no common parameter coordinate, the active index set must
consist of EXACTLY two distinct lines, and their parameter sets
must be disjoint. This removes any three-line minimal-transverse
history obstruction in the rank-two case, without ever replacing
the weak source by its image or closure.

This is precisely the setting for the genuine two-copy overlap
A-letter-root theorem of PR #169. But neither result proves that
the induced source is a FREE union of its two line-image pieces:
crossing pure-core relation tuples remain possible, as explicitly
witnessed by the Boolean power regression PR #170.

Thus the rank-two transverse branch is reduced to a single pair
and the still-open free-source/K-boundary gluing issue. There is no
claim of a complete rank-two Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment
open StructuralRamsey.HalesJewett

universe u v
variable {L : RelLanguage.{u}}

/-- A finite at-most-two genuine HJ line family with NO shared
parameter must be exactly two distinct lines with DISJOINT
parameter-coordinate sets. N>0 makes the empty family GOOD;
individual lines are GOOD by their required parameter witness. -/
theorem native2019_at_most_two_bad_HJ_lines_are_transverse
    {I Alphabet : Type v} {N : ℕ}
    [DecidableEq I]
    (lines : I → Line Alphabet N)
    (T : Finset I)
    (hN : 0 < N)
    (hCard : T.card ≤ 2)
    (hBad : ¬ ∃ k : Fin N,
      ∀ i ∈ T, (lines i).symbol k = .parameter) :
    ∃ i j : I, i ≠ j ∧ T = {i,j} ∧
      ∀ k : Fin N,
        (lines i).symbol k = .parameter →
        (lines j).symbol k ≠ .parameter := by
  classical
  have hTwo : T.card = 2 := by
    by_contra hne
    have hSmall : T.card ≤ 1 := by omega
    interval_cases hc : T.card
    · have hEmpty : T = ∅ := Finset.card_eq_zero.mp hc
      apply hBad
      refine ⟨⟨0, hN⟩, ?_⟩
      intro i hi
      simp [hEmpty] at hi
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
      obtain ⟨k, hk⟩ := (lines i).hasParameter
      apply hBad
      refine ⟨k, ?_⟩
      intro j hj
      have hji : j = i := by simpa [hi] using hj
      subst j
      exact hk
  obtain ⟨i, j, hij, hT⟩ := Finset.card_eq_two.mp hTwo
  refine ⟨i, j, hij, hT, ?_⟩
  intro k hi hj
  apply hBad
  refine ⟨k, ?_⟩
  intro t ht
  rw [hT] at ht
  rcases Finset.mem_insert.mp ht with hti | htj
  · subst t
    exact hi
  · have htj' : t = j := Finset.mem_singleton.mp htj
    subst t
    exact hj

/-- Apply the genuine NONINJECTIVE POSITIVE native generator bound
to conclude: any source with intrinsic USize<=2 and genuinely bad
private-active HJ history has EXACTLY two active indices, with
transverse parameter sets. The required relative U-closedness of
the actual attaching support is explicit, not guessed. -/
theorem native2019_positive_rank_two_bad_history_is_pair
    {rules : ClosureDescription L}
    {U V W I Alphabet : Type v} {N : ℕ}
    [Fintype U] [DecidableEq I]
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (hSupport : IsUSubstructure rules Old Support)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphism (attach Old Support Core maps) p)
    (lines : I → Line Alphabet N)
    (hN : 0 < N)
    (hRank : USize rules Source ≤ 2)
    (hBad : ¬ ∃ k : Fin N,
      ∀ i ∈ native2019_exact_active_index_finset Support p,
        (lines i).symbol k = .parameter) :
    ∃ i j : I, i ≠ j ∧
      native2019_exact_active_index_finset Support p = {i,j} ∧
      ∀ k : Fin N,
        (lines i).symbol k = .parameter →
        (lines j).symbol k ≠ .parameter := by
  classical
  have hBound :
      (native2019_exact_active_index_finset Support p).card ≤ 2 :=
    (native2019_positive_active_index_card_le_USize
      Source Old Support Core maps hSupport p hp).trans hRank
  exact native2019_at_most_two_bad_HJ_lines_are_transverse
    lines (native2019_exact_active_index_finset Support p)
    hN hBound hBad

end AllThoseRamseyClasses.Published
