import PartiteConstruction.Ramsey.ClosureGeneratedHullRank

/-!
# Definition 2.25 (2019): correct U-size bound for weak ambient closure

The sentence immediately following the published Definition 2.25
claims equality of intrinsic U-size between an arbitrary WEAK induced
test and its U-closure in a U-closed ambient structure. This is false.

A three-vertex example with roots a,b closing to r and a root r
closing back to (a,b) has a weak two-vertex test of U-size 2 whose
ambient U-closure has U-size 1. The example and finite regression
are explained in partite-construction's
docs/theorem218-U-size-closure-strict-drop.md.

The valid statement is a one-sided inequality:

    USize (A | cl_A(S)) <= USize (A | S).

Indeed, a minimum intrinsic generating set G of the ORIGINAL weak
test A|S generates the whole ambient closure cl_A(S). One must NOT
assert that the two U-sizes are equal or replace a tested weak set
by its hull in Definition 2.17(4c).

The proof below follows the independently developed
partite-construction/ClosureWeakHullUSize.lean argument, but is
rechecked against the 2019 formalization's pinned dependency.
No additional axioms, target-class assumptions, or closures of the
tested source are introduced.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- Any U-generating set G of the exact weak induced structure A|S
generates the entire ambient U-closure of S. Neither A nor A|S is
assumed intrinsically closed. The two AMBIENT hulls are equal. -/
theorem weak_induced_generators_ambientHull_eq_2019
    (rules : ClosureDescription L)
    (A : RelStructure L V) (S : Set V) (G : Set S)
    (hGen : IsUGenerating rules (A.induce S) G) :
    UClosureHull rules A (Subtype.val '' G) =
      UClosureHull rules A S := by
  let H : Set V := UClosureHull rules A (Subtype.val '' G)
  have hH : IsUSubstructure rules A H :=
    UClosureHull_isUSubstructure rules A (Subtype.val '' G)
  have hPre : IsUSubstructure rules (A.induce S)
      (Subtype.val ⁻¹' H) :=
    hH.preimage_embedding (inclusion A S)
  have hGPre : G ⊆ (Subtype.val ⁻¹' H) := by
    intro g hg
    exact subset_UClosureHull rules A (Subtype.val '' G)
      ⟨g, hg, rfl⟩
  have hS : S ⊆ H := by
    intro x hx
    have hAll : (⟨x, hx⟩ : S) ∈
        UClosureHull rules (A.induce S) G := by
      rw [hGen]
      trivial
    exact UClosureHull_minimal rules (A.induce S)
      hPre hGPre hAll
  apply Set.Subset.antisymm
  · apply UClosureHull_mono rules A
    rintro x ⟨g, hg, rfl⟩
    exact g.2
  · exact UClosureHull_minimal rules A hH hS

/-- Correct replacement for the printed U-size equality after
Definition 2.25. The original weak induced test and the ambient
generated hull are kept as distinct relational structures.

No U-closedness assumption on A is required for this inequality. -/
theorem USize_ambientHull_le_weak_2019
    [Fintype V]
    (rules : ClosureDescription L)
    (A : RelStructure L V) (S : Set V)
    [Fintype S] [Fintype (UClosureHull rules A S)] :
    USize rules (A.induce (UClosureHull rules A S)) ≤
      USize rules (A.induce S) := by
  classical
  let H : Set V := UClosureHull rules A S
  obtain ⟨G, hGCard, hGGen⟩ := USize_spec rules (A.induce S)
  let e : S ↪ H := {
    toFun := fun s => ⟨s.1, subset_UClosureHull rules A S s.2⟩
    inj' := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : H => z.1) hxy
  }
  let GH : Finset H := G.map e
  have hHullEq : UClosureHull rules A
      (Subtype.val '' (↑G : Set S)) = H :=
    weak_induced_generators_ambientHull_eq_2019
      rules A S (↑G : Set S) hGGen
  have hOnH : IsUGenerating rules (A.induce H)
      {x : H | x.1 ∈ Subtype.val '' (↑G : Set S)} := by
    have h := UClosureHull_induce_generated rules A
      (Subtype.val '' (↑G : Set S))
    rw [hHullEq] at h
    exact h
  have hSet : (↑GH : Set H) =
      {x : H | x.1 ∈ Subtype.val '' (↑G : Set S)} := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hse⟩ := Finset.mem_map.mp hx
      exact ⟨s, hs, congrArg Subtype.val hse⟩
    · rintro ⟨s, hs, hse⟩
      apply Finset.mem_map.mpr
      refine ⟨s, hs, ?_⟩
      apply Subtype.ext
      exact hse
  have hGenH : IsUGenerating rules (A.induce H) (↑GH : Set H) := by
    rw [hSet]
    exact hOnH
  calc
    USize rules (A.induce H) ≤ GH.card :=
      USize_le_of_generating rules (A.induce H) GH hGenH
    _ = G.card := by simp [GH]
    _ = USize rules (A.induce S) := hGCard

end AllThoseRamseyClasses.Published
