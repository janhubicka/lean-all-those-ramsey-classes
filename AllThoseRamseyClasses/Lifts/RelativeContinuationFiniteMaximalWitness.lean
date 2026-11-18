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


/-- Genuine finite-index version: the type `P` represents finitely
many possible continuation ROWS, whereas `C` is the (possibly
infinite) universe of all rooted continuation tests. Under extension,
a row can only gain tests. An extension exists whose row becomes
unchanged under every further extension, even though the test
universe itself need not be finite.

The proof applies finite-subset saturation to the DOWNSETS of
rows inside the finite type `P`. Equality of downsets and row
monotonicity imply equality of the full, potentially infinite rows.
-/
theorem exists_stable_finite_index_continuation_row
    {P : Type v} {C : Type u} [Fintype P]
    (extendsRel : W → W → Prop)
    (rowType : W → P)
    (holds : P → C → Prop)
    (hrefl : ∀ w : W, extendsRel w w)
    (htrans : ∀ a b c : W,
      extendsRel a b → extendsRel b c → extendsRel a c)
    (hmono : ∀ a b : W, extendsRel a b →
      ∀ t : C, holds (rowType a) t → holds (rowType b) t)
    (a : W) :
    ∃ b : W, extendsRel a b ∧
      ∀ c : W, extendsRel b c →
        ∀ t : C, holds (rowType c) t ↔ holds (rowType b) t := by
  classical
  let down : W → Finset P := fun w =>
    Finset.univ.filter (fun q => ∀ t : C,
      holds q t → holds (rowType w) t)
  have hdown : ∀ x y : W, extendsRel x y → down x ⊆ down y := by
    intro x y hxy p hp
    simp only [down, Finset.mem_filter, Finset.mem_univ, true_and]
      at hp ⊢
    intro t ht
    exact hmono x y hxy t (hp t ht)
  obtain ⟨b, hab, hstable⟩ :=
    exists_stable_finite_continuation_profile
      extendsRel down hrefl htrans hdown a
  refine ⟨b, hab, ?_⟩
  intro c hbc t
  have hself : rowType c ∈ down c := by
    simp only [down, Finset.mem_filter, Finset.mem_univ, true_and]
    intro s hs
    exact hs
  have hmem : rowType c ∈ down b := by
    rw [← hstable c hbc]
    exact hself
  have hcb : ∀ s : C, holds (rowType c) s → holds (rowType b) s := by
    simpa only [down, Finset.mem_filter, Finset.mem_univ, true_and]
      using hmem
  exact ⟨fun ht => hcb t ht, fun ht => hmono b c hbc t ht⟩

end AllThoseRamseyClasses.Lifts
