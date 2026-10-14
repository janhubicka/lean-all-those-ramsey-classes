import AllThoseRamseyClasses.Applications.SteinerStrongEmbedding
import PartiteConstruction.Ramsey.ClosureClosedLocalFiniteness

/-!
# Closed heredity of ordered partial Steiner triples

A full embedded U-closed source is again a well-formed partial Steiner
system. In the only nontrivial case, a marked pair in the source gets
its block COMPLETION INSIDE the source by intrinsic U-closedness.
An arbitrary nonclosed induced subset need not be a member of K.

This verifies exactly the (2) closed-heredity clause of the repaired
2019 multiamalgamation criterion, not the full Ramsey application.
-/

namespace AllThoseRamseyClasses.Applications.SteinerTriples

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- An ordered marked pair of the smaller structure induces the
same full two-vertex root as its image in the larger K-member. -/
theorem covered_root_of_embedding
    {U V : Type} {A : RelStructure Lang U} {B : RelStructure Lang V}
    (e : Embedding A B) (hB : IsOrderedPartialSteinerTriple B)
    (x y : U) (hCovered : edge A .covered x y) :
    ∃ q : Embedding pairRoot A, q 0 = x ∧ q 1 = y := by
  classical
  have hBCovered : edge B .covered (e x) (e y) :=
    (edge_embedding_iff e .covered x y).mpr hCovered
  obtain ⟨r, hr0, hr1⟩ := hB.covered_root (e x) (e y) hBCovered
  have hRange : ∀ i : Fin 2, ∃ a : U, r i = e a := by
    intro i
    fin_cases i
    · exact ⟨x, hr0⟩
    · exact ⟨y, hr1⟩
  let q : Embedding pairRoot A := r.factorThroughRange e hRange
  have hq (i : Fin 2) : e (q i) = r i := by
    change e (Classical.choose (hRange i)) = r i
    exact (Classical.choose_spec (hRange i)).symm
  refine ⟨q, ?_, ?_⟩
  · apply e.injective
    calc
      e (q 0) = r 0 := hq 0
      _ = e x := hr0
  · apply e.injective
    calc
      e (q 1) = r 1 := hq 1
      _ = e y := hr1

/-- The 2019 intrinsic-closedness hypothesis is precisely what
prevents a covered pair from losing its uniquely designated block. -/
theorem orderedSteiner_of_closed_embedding
    {U V : Type}
    (A : RelStructure Lang U) (B : RelStructure Lang V)
    (hB : IsOrderedPartialSteinerTriple B)
    (hA : IsUClosed blockRules A)
    (e : Embedding A B) :
    IsOrderedPartialSteinerTriple A := by
  classical
  haveI : Finite V := hB.finite
  refine {
    finite := Finite.of_injective e e.injective
    order_irrefl := ?_
    order_trans := ?_
    order_total := ?_
    covered_implies_order := ?_
    covered_root := ?_
    block_valid := ?_
    block_distinct := ?_
    covered_has_block := ?_
    block_unique := ?_
    other_pairs := ?_
  }
  · intro x hx
    exact hB.order_irrefl (e x)
      ((edge_embedding_iff e .order x x).mpr hx)
  · intro x y z hxy hyz
    apply (edge_embedding_iff e .order x z).mp
    exact hB.order_trans (e x) (e y) (e z)
      ((edge_embedding_iff e .order x y).mpr hxy)
      ((edge_embedding_iff e .order y z).mpr hyz)
  · intro x y hxy
    rcases hB.order_total (e x) (e y) (fun heq => hxy (e.injective heq)) with h | h
    · exact Or.inl ((edge_embedding_iff e .order x y).mp h)
    · exact Or.inr ((edge_embedding_iff e .order y x).mp h)
  · intro x y hxy
    apply (edge_embedding_iff e .order x y).mp
    exact hB.covered_implies_order (e x) (e y)
      ((edge_embedding_iff e .covered x y).mpr hxy)
  · intro x y hxy
    exact covered_root_of_embedding e hB x y hxy
  · intro x y z h
    apply (edge_embedding_iff e .covered x y).mp
    exact hB.block_valid (e x) (e y) (e z)
      ((triple_embedding_iff e x y z).mpr h)
  · intro x y z h
    obtain ⟨hxy, hxz, hyz⟩ := hB.block_distinct (e x) (e y) (e z)
      ((triple_embedding_iff e x y z).mpr h)
    exact ⟨fun h => hxy (congrArg e h),
      fun h => hxz (congrArg e h),
      fun h => hyz (congrArg e h)⟩
  · intro x y hxy
    obtain ⟨q, hq0, hq1⟩ := covered_root_of_embedding e hB x y hxy
    have hrule : blockRule ∈ blockRules := by simp [blockRules]
    obtain ⟨t, ht, _⟩ := (hA blockRule hrule).2 q
    refine ⟨t 2, ?_⟩
    have ht0 : t 0 = x := (ht.2 0).trans hq0
    have ht1 : t 1 = y := (ht.2 1).trans hq1
    have heq : (![x, y, t 2] : Fin 3 → U) = t := by
      funext i
      fin_cases i
      · exact ht0.symm
      · exact ht1.symm
      · rfl
    change A.rel .block ![x, y, t 2]
    rw [heq]
    exact ht.1
  · intro x y z w hz hw
    apply e.injective
    exact hB.block_unique (e x) (e y) (e z) (e w)
      ((triple_embedding_iff e x y z).mpr hz)
      ((triple_embedding_iff e x y w).mpr hw)
  · intro x y z hz
    obtain ⟨hXZ, hYZ⟩ := hB.other_pairs (e x) (e y) (e z)
      ((triple_embedding_iff e x y z).mpr hz)
    constructor
    · rcases hXZ with ⟨htr, hord⟩ | ⟨htr, hord⟩
      · exact Or.inl ⟨(triple_embedding_iff e x z y).mp htr,
          (edge_embedding_iff e .order x z).mp hord⟩
      · exact Or.inr ⟨(triple_embedding_iff e z x y).mp htr,
          (edge_embedding_iff e .order z x).mp hord⟩
    · rcases hYZ with ⟨htr, hord⟩ | ⟨htr, hord⟩
      · exact Or.inl ⟨(triple_embedding_iff e y z x).mp htr,
          (edge_embedding_iff e .order y z).mp hord⟩
      · exact Or.inr ⟨(triple_embedding_iff e z y x).mp htr,
          (edge_embedding_iff e .order z y).mp hord⟩

theorem orderedSteiner_closedUHereditary :
    ClosedUHereditary orderedSteinerClass blockRules := by
  intro U V A B hB hA e
  exact orderedSteiner_of_closed_embedding A B hB hA e

end AllThoseRamseyClasses.Applications.SteinerTriples
