import AllThoseRamseyClasses.Published.ExactFreeCoverTupleLocalization2019

/-!
# Exact three-vertex source geometry, for arbitrary relational arities

A reducible source on at most three vertices either has an isolated
vertex, giving a disjoint free cover by two pieces of size at most two,
or is freely covered by two ordinary irreducible induced pieces.
This is source tuple geometry, not an assumption on Hales--Jewett lines.
Nullary relations are allowed throughout.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- A source subset with only two possible values is irreducible when
one relation tuple inside it witnesses the two values together. -/
theorem exact2019_two_value_tuple_irreducible
    {X : Type v} (Source : RelStructure L X)
    (S : Set X) (a b : X)
    (hValues : ∀ x : S, x.1 = a ∨ x.1 = b)
    (R : L.Symbol) (z : Fin (L.arity R) → X)
    (i j : Fin (L.arity R)) (hz : Source.rel R z)
    (hRange : ∀ k, z k ∈ S) (hi : z i = a) (hj : z j = b) :
    (Source.induce S).Irreducible := by
  let zz : Fin (L.arity R) → S := fun k => ⟨z k, hRange k⟩
  intro x y hxy
  rcases hValues x with hx | hx <;> rcases hValues y with hy | hy
  · exact (hxy (Subtype.ext (hx.trans hy.symm))).elim
  · exact ⟨R, zz, i, j, hz,
      Subtype.ext (hi.trans hx.symm), Subtype.ext (hj.trans hy.symm)⟩
  · exact ⟨R, zz, j, i, hz,
      Subtype.ext (hj.trans hx.symm), Subtype.ext (hi.trans hy.symm)⟩
  · exact (hxy (Subtype.ext (hx.trans hy.symm))).elim

/-- Every reducible exact source on at most THREE vertices has either
a disjoint free cover with both sides of size at most two, or a free
cover by TWO ordinary irreducible pieces. The cover and tuple clauses
are on the original source, without replacing it by any closure. -/
theorem exact2019_three_vertex_free_cover_dichotomy
    {X : Type v} [Fintype X] (Source : RelStructure L X)
    (hCard : Fintype.card X ≤ 3) (hNotIrred : ¬ Source.Irreducible) :
    ∃ S T : Set X,
      (∀ x, x ∈ S ∨ x ∈ T) ∧
      (∀ R (z : Fin (L.arity R) → X), Source.rel R z →
        (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T)) ∧
      ((Disjoint S T ∧ Nat.card S ≤ 2 ∧ Nat.card T ≤ 2) ∨
        ((Source.induce S).Irreducible ∧ (Source.induce T).Irreducible)) := by
  classical
  let Occur : X → X → Prop := fun a b =>
    ∃ (R : L.Symbol) (z : Fin (L.arity R) → X)
      (i j : Fin (L.arity R)), Source.rel R z ∧ z i = a ∧ z j = b
  by_cases hIsolated : ∃ a : X, ∀ b : X, b ≠ a → ¬ Occur a b
  · obtain ⟨a, ha⟩ := hIsolated
    let S : Set X := {a}
    let T : Set X := {x | x ≠ a}
    letI : Fintype S := Fintype.ofFinite S
    letI : Fintype T := Fintype.ofFinite T
    have hSCard : Fintype.card S ≤ 1 := by
      have hFin : (Finset.univ : Finset S).card ≤ 1 :=
        Finset.card_le_one.mpr (by
          intro x _ y _
          apply Subtype.ext
          exact (show x.1 = a from x.2).trans (show y.1 = a from y.2).symm)
      simpa using hFin
    have hTCard : Fintype.card T < Fintype.card X :=
      Fintype.card_lt_of_injective_not_surjective
        (Subtype.val : T → X) Subtype.val_injective (by
          intro hSurj
          obtain ⟨x, hx⟩ := hSurj a
          exact x.2 hx)
    refine ⟨S, T, ?_, ?_, Or.inl ⟨?_, ?_, ?_⟩⟩
    · intro x
      by_cases hx : x = a
      · exact Or.inl hx
      · exact Or.inr hx
    · intro R z hz
      by_cases hHit : ∃ i, z i = a
      · obtain ⟨i, hi⟩ := hHit
        left
        intro k
        by_contra hk
        exact ha (z k) hk ⟨R, z, i, k, hz, hi, rfl⟩
      · right
        intro k hk
        exact hHit ⟨k, hk⟩
    · apply Set.disjoint_left.mpr
      intro x hxS hxT
      exact hxT hxS
    · simpa only [Nat.card_eq_fintype_card] using (show Fintype.card S ≤ 2 by omega)
    · simpa only [Nat.card_eq_fintype_card] using (show Fintype.card T ≤ 2 by omega)
  · have hNeighbor : ∀ a : X, ∃ b : X, b ≠ a ∧ Occur a b := by
      intro a
      by_contra h
      apply hIsolated
      refine ⟨a, ?_⟩
      intro b hba hab
      exact h ⟨b, hba, hab⟩
    have hPair : ∃ a b : X, a ≠ b ∧ ¬ Occur a b := by
      by_contra h
      apply hNotIrred
      intro a b hab
      by_contra hNoTuple
      exact h ⟨a, b, hab, hNoTuple⟩
    obtain ⟨a, b, hab, hSep⟩ := hPair
    obtain ⟨c, hca, hAC⟩ := hNeighbor a
    have hcb : c ≠ b := by
      intro h
      obtain ⟨R, z, i, j, hz, hi, hj⟩ := hAC
      exact hSep ⟨R, z, i, j, hz, hi, hj.trans h⟩
    have hExhaust : ∀ x : X, x = a ∨ x = b ∨ x = c := by
      intro x
      by_cases hxa : x = a
      · exact Or.inl hxa
      by_cases hxb : x = b
      · exact Or.inr (Or.inl hxb)
      by_cases hxc : x = c
      · exact Or.inr (Or.inr hxc)
      have hBound : ({a, b, c, x} : Finset X).card ≤ Fintype.card X :=
        Finset.card_le_univ _
      have hFour : ({a, b, c, x} : Finset X).card = 4 := by
        simp [hab, hca, hcb, hxa, hxb, hxc, Ne.symm hab,
          Ne.symm hca, Ne.symm hcb, Ne.symm hxa, Ne.symm hxb, Ne.symm hxc]
      omega
    obtain ⟨d, hdb, hBD⟩ := hNeighbor b
    have hda : d ≠ a := by
      intro h
      obtain ⟨R, z, i, j, hz, hi, hj⟩ := hBD
      exact hSep ⟨R, z, j, i, hz, hj.trans h, hi⟩
    have hdc : d = c := by
      rcases hExhaust d with h | h | h
      · exact (hda h).elim
      · exact (hdb h).elim
      · exact h
    have hBC : Occur b c := hdc ▸ hBD
    let S : Set X := {x | x ≠ b}
    let T : Set X := {x | x ≠ a}
    have hValuesS : ∀ x : S, x.1 = a ∨ x.1 = c := by
      intro x
      rcases hExhaust x.1 with h | h | h
      · exact Or.inl h
      · exact (x.2 h).elim
      · exact Or.inr h
    have hValuesT : ∀ x : T, x.1 = b ∨ x.1 = c := by
      intro x
      rcases hExhaust x.1 with h | h | h
      · exact (x.2 h).elim
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨Rac, zac, iac, jac, hRelAC, hACa, hACc⟩ := hAC
    have hRangeAC : ∀ k, zac k ∈ S := by
      intro k hk
      exact hSep ⟨Rac, zac, iac, k, hRelAC, hACa, hk⟩
    obtain ⟨Rbc, zbc, ibc, jbc, hRelBC, hBCb, hBCc⟩ := hBC
    have hRangeBC : ∀ k, zbc k ∈ T := by
      intro k hk
      exact hSep ⟨Rbc, zbc, k, ibc, hRelBC, hk, hBCb⟩
    have hSIrred : (Source.induce S).Irreducible :=
      exact2019_two_value_tuple_irreducible Source S a c hValuesS
        Rac zac iac jac hRelAC hRangeAC hACa hACc
    have hTIrred : (Source.induce T).Irreducible :=
      exact2019_two_value_tuple_irreducible Source T b c hValuesT
        Rbc zbc ibc jbc hRelBC hRangeBC hBCb hBCc
    refine ⟨S, T, ?_, ?_, Or.inr ⟨hSIrred, hTIrred⟩⟩
    · intro x
      by_cases hxb : x = b
      · right
        change x ≠ a
        simpa [hxb] using hab.symm
      · exact Or.inl hxb
    · intro R z hz
      by_cases hS : ∀ k, z k ≠ b
      · exact Or.inl hS
      · push Not at hS
        obtain ⟨j, hj⟩ := hS
        right
        intro k hk
        exact hSep ⟨R, z, k, j, hz, hk, hj⟩

end AllThoseRamseyClasses.Published
