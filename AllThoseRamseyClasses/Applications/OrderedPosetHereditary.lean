import AllThoseRamseyClasses.Applications.OrderedPosetClass
import AllThoseRamseyClasses.Published.InducedClosed2019HereditaryBridge

/-!
# Actual induced and embedded heredity of finite ordered posets

The ordered-poset class is NOT just the class of all arbitrary
ordered binary structures. For every FULL relational embedding
into a genuine member, we reflect the named linear order, partial
order, and the inert symbol. This validates the exact target class
in the corrected 2019 application, including isomorphism invariance
needed for the coordinated class API.

This module proves NO strong amalgamation or exact local completion
and makes NO standalone Ramsey assertion.
-/

namespace AllThoseRamseyClasses.Applications.OrderedPosets

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published
open AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- An ordinary full relational embedding exactly preserves and
reflects each two-vertex relation, including the named order. -/
theorem edge_embedding_iff
    {U V : Type}
    {A : RelStructure Lang U} {B : RelStructure Lang V}
    (e : Embedding A B)
    (R : Symbol) (x y : U) :
    edge B R (e x) (e y) ↔ edge A R x y := by
  have ht : e ∘ ![x, y] = ![e x, e y] := by
    funext i
    fin_cases i <;> rfl
  change B.rel R ![e x, e y] ↔ A.rel R ![x, y]
  rw [← ht]
  exact e.map_rel_iff R ![x, y]

/-- Every full embedded substructure of an ordered poset is a member.
In particular, the ambient finite-order/strictness and all negative
E- and M-information are preserved and reflected. -/
theorem orderedPosetClass_hereditary
    {U V : Type}
    {A : RelStructure Lang U} {B : RelStructure Lang V}
    (hB : orderedPosetClass B) (e : Embedding A B) :
    orderedPosetClass A := by
  letI : Finite V := hB.1.1
  letI : Finite U := Finite.of_injective e e.injective
  have hAmbient : orderedAmbientClass A := by
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · intro x hx
      exact (hB.1.2.1 (e x)) ((edge_embedding_iff e .lt x x).mpr hx)
    · intro x y z hxy hyz
      apply (edge_embedding_iff e .lt x z).mp
      exact hB.1.2.2.1 (e x) (e y) (e z)
        ((edge_embedding_iff e .lt x y).mpr hxy)
        ((edge_embedding_iff e .lt y z).mpr hyz)
    · intro x y hne
      have heNe : e x ≠ e y := fun heq => hne (e.injective heq)
      rcases hB.1.2.2.2 (e x) (e y) heNe with hlt | hgt
      · exact Or.inl ((edge_embedding_iff e .lt x y).mp hlt)
      · exact Or.inr ((edge_embedding_iff e .lt y x).mp hgt)
  refine ⟨hAmbient, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (edge_embedding_iff e .equiv x x).mp (hB.2.1 (e x))
  · intro x y z hxy hyz
    apply (edge_embedding_iff e .equiv x z).mp
    exact hB.2.2.1 (e x) (e y) (e z)
      ((edge_embedding_iff e .equiv x y).mpr hxy)
      ((edge_embedding_iff e .equiv y z).mpr hyz)
  · intro x y hxy hyx
    apply e.injective
    exact hB.2.2.2.1 (e x) (e y)
      ((edge_embedding_iff e .equiv x y).mpr hxy)
      ((edge_embedding_iff e .equiv y x).mpr hyx)
  · intro x y hne hxy
    apply (edge_embedding_iff e .lt x y).mp
    exact hB.2.2.2.2.1 (e x) (e y)
      (fun heq => hne (e.injective heq))
      ((edge_embedding_iff e .equiv x y).mpr hxy)
  · intro x y h
    exact (hB.2.2.2.2.2 (e x) (e y))
      ((edge_embedding_iff e .mate x y).mpr h)

/-- A class predicate is not automatically isomorphism-invariant.
For this specific class, full embedded heredity implies the exact
coordinated 2019 isomorphism condition. -/
theorem orderedPosetClass_isomorphismClosed :
    IsomorphismClosed2019 orderedPosetClass := by
  intro X Y A B e _ hB
  exact orderedPosetClass_hereditary hB e

/-- Original induced-substructure clause, with no closure needed. -/
theorem orderedPosetClass_induced_hereditary
    {V : Type} (B : RelStructure Lang V)
    (hB : orderedPosetClass B) (S : Set V) :
    orderedPosetClass (B.induce S) :=
  orderedPosetClass_hereditary hB (RelStructure.inclusion B S)

end AllThoseRamseyClasses.Applications.OrderedPosets
