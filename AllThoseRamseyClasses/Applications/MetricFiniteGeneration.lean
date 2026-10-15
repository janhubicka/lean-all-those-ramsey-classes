import AllThoseRamseyClasses.FiniteSemigroup
import AllThoseRamseyClasses.Applications.MetricCappedAlgebra

/-!
# Finite associative distance extensions

Given a positive distance set whose rounded sum is well-defined and
associative, every finite set of its distances lies in a finite subset
whose own rounded sum is again well-defined and associative.

The proof uses the actual generated subsemigroup of distances below a cap,
not a hypothetical finite closure. The empty generating set needs no cap
and is handled separately. This is the finite-distance reduction used in
`prop:Smetric`, not the complete convexly ordered metric Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

/-- Finite generation under an allowed cap, with the exact restricted-operation
properties returned alongside the finite closed set. -/
theorem exists_finite_capped_extension {S D : Set ℝ} {m : ℝ}
    (hpos : Positive S) (hS : WellDefined S) (hassoc : AssociativeOn S)
    (hm : m ∈ S) (hD : D.Finite) (hDS : D ⊆ S)
    (hDm : ∀ d ∈ D, d ≤ m) :
    ∃ T : Set ℝ, T.Finite ∧ D ⊆ T ∧ T ⊆ S ∧
      (∀ t ∈ T, t ≤ m) ∧
      (∀ a ∈ T, ∀ b ∈ T, cappedSum S m a b ∈ T) ∧
      WellDefined T ∧ AssociativeOn T := by
  let X := {a : ℝ // a ∈ S ∧ a ≤ m}
  letI : CommSemigroup X := {
    mul := fun a b => ⟨cappedSum S m a.val b.val,
      cappedSum_mem hS hm a.property.1 b.property.1, min_le_left _ _⟩
    mul_assoc := by
      intro a b c
      apply Subtype.ext
      exact cappedSum_assoc hpos hS hassoc hm a.property.1 b.property.1 c.property.1
    mul_comm := by
      intro a b
      apply Subtype.ext
      exact cappedSum_comm S m a.val b.val
  }
  have hpower : ∀ (a : X) (n : ℕ),
      (FiniteSemigroup.positivePower a n).val = power S m a.val n := by
    intro a n
    induction n with
    | zero => rfl
    | succ n ih =>
        change cappedSum S m (FiniteSemigroup.positivePower a n).val a.val =
          cappedSum S m (power S m a.val n) a.val
        rw [ih]
  let E : Set X := (fun a : X => a.val) ⁻¹' D
  have hE : E.Finite :=
    Set.Finite.preimage (fun x _ y _ h => Subtype.ext h) hD
  have hG : (Subsemigroup.closure E : Set X).Finite := by
    apply FiniteSemigroup.finite_closure E hE
    intro a _ha
    have hf := finite_range_power hS hm a.property.1
      (hpos a.val a.property.1) a.property.2
    have hpre : ((fun x : X => x.val) ⁻¹' Set.range (power S m a.val)).Finite :=
      Set.Finite.preimage (fun x _ y _ h => Subtype.ext h) hf
    apply hpre.subset
    rintro _ ⟨n, rfl⟩
    exact ⟨n, (hpower a n).symm⟩
  let G : Subsemigroup X := Subsemigroup.closure E
  let T : Set ℝ := (fun a : X => a.val) '' (G : Set X)
  have hT : T.Finite := hG.image (fun a : X => a.val)
  have hDT : D ⊆ T := by
    intro a ha
    refine ⟨⟨a, hDS ha, hDm a ha⟩, ?_, rfl⟩
    exact Subsemigroup.subset_closure ha
  have hTS : T ⊆ S := by
    rintro _ ⟨a, _ha, rfl⟩
    exact a.property.1
  have hTm : ∀ t ∈ T, t ≤ m := by
    rintro _ ⟨a, _ha, rfl⟩
    exact a.property.2
  have hclosed : ∀ a ∈ T, ∀ b ∈ T, cappedSum S m a b ∈ T := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a * b, G.mul_mem ha hb, rfl⟩
  exact ⟨T, hT, hDT, hTS, hTm, hclosed,
    wellDefined_subset hpos hTS hTm hclosed,
    associativeOn_subset hpos hS hassoc hm hTS hTm hclosed⟩

/-- Every finite set of allowed distances has a finite associative distance
extension. Empty S and empty D are allowed and require no maximum choice. -/
theorem exists_finite_distance_extension {S D : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S) (hassoc : AssociativeOn S)
    (hD : D.Finite) (hDS : D ⊆ S) :
    ∃ T : Set ℝ, T.Finite ∧ D ⊆ T ∧ T ⊆ S ∧
      WellDefined T ∧ AssociativeOn T := by
  classical
  by_cases hne : D.Nonempty
  · let F : Finset ℝ := hD.toFinset
    have hF : F.Nonempty := by
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, hD.mem_toFinset.mpr ha⟩
    let m := F.max' hF
    have hmD : m ∈ D := hD.mem_toFinset.mp (Finset.max'_mem F hF)
    have hDm : ∀ d ∈ D, d ≤ m := by
      intro d hd
      exact Finset.le_max' F d (hD.mem_toFinset.mpr hd)
    obtain ⟨T, hT, hDT, hTS, _hTm, _hclosed, hTw, hTa⟩ :=
      exists_finite_capped_extension hpos hS hassoc (hDS hmD) hD hDS hDm
    exact ⟨T, hT, hDT, hTS, hTw, hTa⟩
  · have hDE : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst D
    refine ⟨∅, Set.finite_empty, Set.Subset.rfl, Set.empty_subset S, ?_, ?_⟩
    · intro a ha
      exact False.elim ha
    · intro a ha
      exact False.elim ha

end AllThoseRamseyClasses.Applications.MetricSaturation
