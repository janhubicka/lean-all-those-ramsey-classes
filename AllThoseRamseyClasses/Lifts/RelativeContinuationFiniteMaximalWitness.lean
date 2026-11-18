import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-!
# Finite continuation profiles admit finite maximal witnesses

This is the abstract finite-index step of the corrected Section 3
homogenization theorem. Once every finite old root has only finitely
many distinct continuation profiles, any given finite witness
has a finite extension at which that profile cannot increase.

No choice of a countable or globally saturated witness is needed.
The concrete native functional EHN/free-amalgam lemmas supply
reflexivity, transitivity, and profile monotonicity at the
eventual application. This file contains only the FINITE
combinatorial argument and does not presume a relation-only
lift or the Ramsey property.
-/

namespace AllThoseRamseyClasses.Lifts

universe u v

variable {W : Type u} {I : Type v}
variable [Fintype I] [DecidableEq I]

/-- In any extension preorder carrying a monotone finite set of
forbidden continuation tests, every witness has an extension whose
test set is stable under all subsequent extensions. -/
theorem exists_stable_finite_continuation_profile
    (extendsRel : W → W → Prop)
    (profile : W → Finset I)
    (hrefl : ∀ w : W, extendsRel w w)
    (htrans : ∀ a b c : W, extendsRel a b → extendsRel b c → extendsRel a c)
    (hmono : ∀ a b : W, extendsRel a b → profile a ⊆ profile b)
    (a : W) :
    ∃ b : W, extendsRel a b ∧
      ∀ c : W, extendsRel b c → profile c = profile b := by
  classical
  let feasible : Finset (Finset I) :=
    Finset.univ.filter (fun q : Finset I =>
      ∃ b : W, extendsRel a b ∧ profile b = q)
  let sizes : Finset ℕ := feasible.image Finset.card
  have hfeasible : profile a ∈ feasible := by
    simp only [feasible, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨a, hrefl a, rfl⟩
  have hsizes : sizes.Nonempty := by
    refine ⟨(profile a).card, ?_⟩
    exact Finset.mem_image.mpr ⟨profile a, hfeasible, rfl⟩
  let m : ℕ := sizes.max' hsizes
  have hm : m ∈ sizes := Finset.max'_mem sizes hsizes
  obtain ⟨q, hq, hqcard⟩ := Finset.mem_image.mp hm
  have hqexist : ∃ b : W, extendsRel a b ∧ profile b = q := by
    have ht := (Finset.mem_filter.mp hq).2
    exact ht
  obtain ⟨b, hab, hbq⟩ := hqexist
  refine ⟨b, hab, ?_⟩
  intro c hbc
  have hac : extendsRel a c := htrans a b c hab hbc
  have hcfeasible : profile c ∈ feasible := by
    simp only [feasible, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨c, hac, rfl⟩
  have hsizec : (profile c).card ∈ sizes :=
    Finset.mem_image.mpr ⟨profile c, hcfeasible, rfl⟩
  have hbound : (profile c).card ≤ m :=
    Finset.le_max' sizes _ hsizec
  have hsizeb : (profile b).card = m := by
    calc
      (profile b).card = q.card := by rw [hbq]
      _ = m := hqcard
  have hsubset : profile b ⊆ profile c := hmono b c hbc
  have hcard : (profile c).card ≤ (profile b).card := by
    rw [hsizeb]
    exact hbound
  exact (Finset.eq_of_subset_of_card_le hsubset hcard).symm

end AllThoseRamseyClasses.Lifts
