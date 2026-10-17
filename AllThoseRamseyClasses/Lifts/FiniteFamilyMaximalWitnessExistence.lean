import AllThoseRamseyClasses.Lifts.FiniteFamilyCanonicalMaximality
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Existence of finite-family maximal canonical witnesses

For a FINITE named family of finite functional forbidden sources and
a FINITE embedded OLD root X, there are only finitely many possible
canonical all-component observations on the tuples of X. Every FULL
old embedding preserves existing positive observations.

Given a K-allowed A containing X, choose a K-allowed full extension
B of A whose observation profile on X has maximum cardinality among
ALL such extensions. Any later allowed extension of B can only add
observations, so finiteness plus maximality forces equality. This
constructs an actual maximal witness ALONG X, without assuming AP,
JEP, uniform bounds on allowed extension sizes, or finiteness of B.

This solves maximal-witness EXISTENCE in the alternative FINITE-family
folded lift; it does NOT construct an allowed common free amalgam,
prove AP of the expanded age, or extend the argument to an arbitrary
regular infinite forbidden family.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- One query in the finite-family canonical tag language over a
fixed OLD root. Colliding root coordinates are retained. -/
abbrev FiniteNamedRootObservation
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (UX : Type) :=
  Σ tag : Family.ComponentTag, Fin (tag.width Family) → UX

/-- The universe of tagged-root observations is finite as soon
as the named family and the root carrier are finite. -/
theorem finiteNamedRootObservation_finite
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (UX : Type) [Finite UX] :
    Finite (FiniteNamedRootObservation Family UX) := by
  letI (tag : Family.ComponentTag) :
      Finite (Fin (tag.width Family) → UX) := inferInstance
  infer_instance

/-- All POSITIVE folded canonical component observations on X
seen inside the full old witness embedding iA : X -> A. -/
noncomputable def finiteNamedRootProfile
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UX UA : Type} [Fintype UX]
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A) :
    Finset (FiniteNamedRootObservation Family UX) := by
  classical
  letI : Fintype Family.ComponentTag :=
    Fintype.ofFinite Family.ComponentTag
  exact Finset.univ.filter (fun p =>
    (finiteNamedClosedComponentFoldedLift Family A).rel
      (.inr p.1) (iA ∘ p.2))

/-- Membership in the profile is precisely a true canonical
component-root relation on the corresponding embedded tuple. -/
theorem finiteNamedRootProfile_mem
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UX UA : Type} [Fintype UX]
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A)
    (tag : Family.ComponentTag)
    (xs : Fin (tag.width Family) → UX) :
    (⟨tag, xs⟩ : FiniteNamedRootObservation Family UX) ∈
      finiteNamedRootProfile Family iA ↔
    (finiteNamedClosedComponentFoldedLift Family A).rel
      (.inr tag) (iA ∘ xs) := by
  classical
  simp [finiteNamedRootProfile]

/-- All old full extensions preserve positive component tags
on the designated fixed finite root. This inclusion is the
monotonicity needed for the finite maximization argument. -/
theorem finiteNamedRootProfile_mono
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UX UA UB : Type} [Fintype UX]
    {X : Structure L UX} {A : Structure L UA}
    {B : Structure L UB}
    (iA : Structure.Embedding X A)
    (e : Structure.Embedding A B) :
    finiteNamedRootProfile Family iA ⊆
      finiteNamedRootProfile Family (e.comp iA) := by
  intro p hp
  rcases p with ⟨tag, xs⟩
  have h : (finiteNamedClosedComponentFoldedLift Family A).rel
      (.inr tag) (iA ∘ xs) :=
    (finiteNamedRootProfile_mem Family iA tag xs).mp hp
  have hB :=
    finiteNamedComponentCanonical_relation_map_embedding
      Family e tag (iA ∘ xs) h
  exact (finiteNamedRootProfile_mem Family
    (e.comp iA) tag xs).mpr hB

/-- For ANY K-allowed structure containing a finite root X,
some K-allowed FULL extension is canonical-tag-maximal along
that root. The carrier of the extension is not assumed finite:
only the root profiles form a finite type.

No amalgamation or joint embedding property of K is assumed.
This is the actual existence step missing from the prior
maximality *stability* interface. -/
theorem finiteNamed_exists_maximal_extension
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (K : ∀ {W : Type}, Structure L W → Prop)
    {UX UA : Type} [Fintype UX]
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A)
    (hA : K A) :
    ∃ (UB : Type) (B : Structure L UB),
      K B ∧ ∃ (e : Structure.Embedding A B),
        FiniteNamedCanonicalMaximalAlong Family K
          (e.comp iA) := by
  classical
  let Obs := FiniteNamedRootObservation Family UX
  letI : Finite Obs :=
    finiteNamedRootObservation_finite Family UX
  letI : Finite (Finset Obs) := inferInstance
  let possible : Set (Finset Obs) :=
    {P | ∃ (UB : Type) (B : Structure L UB),
      K B ∧ ∃ (e : Structure.Embedding A B),
        finiteNamedRootProfile Family (e.comp iA) = P}
  letI : Fintype (Finset Obs) := Fintype.ofFinite (Finset Obs)
  let candidates : Finset (Finset Obs) :=
    Finset.univ.filter (fun Q => Q ∈ possible)
  have hNonempty : candidates.Nonempty := by
    refine ⟨finiteNamedRootProfile Family iA, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, ⟨UA, A, hA, Structure.Embedding.id A, rfl⟩⟩
  obtain ⟨P, hP, hBest⟩ :=
    Finset.exists_max_image candidates
      (fun Q : Finset Obs => Q.card) hNonempty
  have hPpossible : P ∈ possible := (Finset.mem_filter.mp hP).2
  obtain ⟨UB, B, hB, e, hEq⟩ := hPpossible
  refine ⟨UB, B, hB, e, ?_⟩
  apply (finiteNamedCanonicalMaximalAlong_iff_no_new
    Family K (e.comp iA)).2
  intro UC C hC eBC tag xs hRelC
  have hExtended : finiteNamedRootProfile Family
        ((eBC.comp e).comp iA) ∈ possible := by
    exact ⟨UC, C, hC, eBC.comp e, rfl⟩
  have hCard : (finiteNamedRootProfile Family
      ((eBC.comp e).comp iA)).card ≤
      (finiteNamedRootProfile Family (e.comp iA)).card := by
    calc
      _ ≤ P.card := hBest _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hExtended⟩)
      _ = _ := by rw [hEq]
  have hMono : finiteNamedRootProfile Family (e.comp iA) ⊆
      finiteNamedRootProfile Family
        ((eBC.comp e).comp iA) :=
    finiteNamedRootProfile_mono Family (e.comp iA) eBC
  have hProfileEq := Finset.eq_of_subset_of_card_le hMono hCard
  have hMemberC :
      (⟨tag, xs⟩ : Obs) ∈ finiteNamedRootProfile Family
        ((eBC.comp e).comp iA) := by
    apply (finiteNamedRootProfile_mem Family
      ((eBC.comp e).comp iA) tag xs).2
    exact hRelC
  have hMemberA :
      (⟨tag, xs⟩ : Obs) ∈ finiteNamedRootProfile Family
        (e.comp iA) := by
    rw [hProfileEq]
    exact hMemberC
  exact (finiteNamedRootProfile_mem Family
    (e.comp iA) tag xs).mp hMemberA

end AllThoseRamseyClasses.Lifts
