import AllThoseRamseyClasses.Published.NativeTwoActivePrivate2019
import AllThoseRamseyClasses.Published.MinimalNoncommonHJ2019

/-!
# Actual Hales--Jewett history: active transverse line family forces a proper cut

Every genuine Hales--Jewett line has at least one parameter coordinate.
Thus a NONEMPTY finite family of genuine lines lacking a single common
parameter coordinate contains at least TWO DISTINCT line indices.
If each line index is genuinely ACTIVE in the exact weak source (it has
at least one source vertex in its private exterior), the two indices
provide precisely the two exclusive-side witnesses proved in PR #142.

This yields a strictly proper relational copy/rest cut with both
source-side sizes <= j for any original exact weak source of <= j+1
vertices. The proof makes no part-label, source-injectivity,
target-semiclosedness or generator-rank assumptions.

Missing: show that the active lines relevant to every truly
uncompletable weak test form such a finite family and localize the
whole test through the selected line subhistory, or supply a separate
completion branch. This lemma does not assert the common A-root,
unconditional Lemma 2.30, or repaired Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment
open StructuralRamsey.HalesJewett

universe u v
variable {L : RelLanguage.{u}}

/-- Any nonempty finite set of GENUINE Hales--Jewett lines with no
common parameter coordinate contains two distinct indices satisfying
an arbitrary predicate which holds for every selected index.

For a singleton, the line's built-in hasParameter contradicts
no-common-coordinate. This is not the false pairwise-intersection
shortcut; no pairwise assumption is used. -/
theorem native2019_noncommon_line_family_has_two_active
    {I Alphabet : Type v} {N : ℕ}
    (lines : I → Line Alphabet N)
    (T : Finset I) (hT : T.Nonempty)
    (hNoCommon : ¬ ∃ k : Fin N,
      ∀ i ∈ T, (lines i).symbol k = .parameter)
    (active : I → Prop)
    (hActive : ∀ i ∈ T, active i) :
    ∃ i j : I, i ≠ j ∧ active i ∧ active j := by
  classical
  obtain ⟨i, hi⟩ := hT
  obtain ⟨k, hk⟩ := (lines i).hasParameter
  have hDifferent : ∃ j : I, j ∈ T ∧ j ≠ i := by
    by_contra h
    apply hNoCommon
    refine ⟨k, ?_⟩
    intro j hj
    by_cases hji : j = i
    · subst j
      exact hk
    · exact False.elim (h ⟨j, hj, hji⟩)
  obtain ⟨j, hj, hji⟩ := hDifferent
  exact ⟨i, j, Ne.symm hji, hActive i hi, hActive j hj⟩

/-- A nonempty family of PRIVATE-ACTIVE native line indices with
no shared HJ parameter coordinate yields an actual proper source
free decomposition with strict side vertex budgets.

The source is the exact weak test. It need not be U-closed; only
ordinary positivity of the native projection is required. -/
theorem native2019_transverse_active_family_small_free_cut
    {U V W I Alphabet : Type v} {N : ℕ}
    [Fintype U]
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphism (attach Old Support Core maps) p)
    (lines : I → Line Alphabet N)
    (T : Finset I) (hT : T.Nonempty)
    (hNoCommon : ¬ ∃ k : Fin N,
      ∀ i ∈ T, (lines i).symbol k = .parameter)
    (hEachActive : ∀ i ∈ T, ∃ x : U,
      OutsideAt (W := W) (I := I) Support i (p x))
    (rank : ℕ) (hCard : Fintype.card U ≤ rank + 1) :
    ∃ d : ProperFreeDecomposition Source,
      Nat.card d.Left ≤ rank ∧ Nat.card d.Right ≤ rank := by
  obtain ⟨i, j, hij, hai, haj⟩ :=
    native2019_noncommon_line_family_has_two_active
      lines T hT hNoCommon
      (fun i => ∃ x : U,
        OutsideAt (W := W) (I := I) Support i (p x))
      hEachActive
  exact native2019_two_active_private_copies_small_sides
    Source Old Support Core maps p hp i j hij rank hCard hai haj

end AllThoseRamseyClasses.Published
