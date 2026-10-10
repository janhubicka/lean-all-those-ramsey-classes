import AllThoseRamseyClasses.Published.FinitePairedClass

/-!
# The ambient ordered relational class in the paired counterexample

The first main multiamalgamation theorem assumes an ambient Ramsey
class R of finite ordinary irreducible structures. Before transferring
the established ordered relational Ramsey theorem along the symbol
renaming (<,E,M) vs (E,M) with a distinguished external order,
we verify its more elementary class-theoretic hypotheses.

This module proves that every finite paired-equivalence object lies
in R and that every member of R is irreducible because its binary
strict total order compares every two distinct vertices. The ambient
Ramsey theorem itself remains an explicit separate obligation.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Finite ordered structures over the SAME language as K, with E and
M interpreted arbitrarily. No matching or equivalence restriction. -/
def orderedAmbientClass : StructureClass (L := Lang) :=
  fun {V} (C : RelStructure Lang V) =>
    Finite V ∧
    (∀ x : V, ¬ edge C .lt x x) ∧
    (∀ x y z : V,
       edge C .lt x y → edge C .lt y z → edge C .lt x z) ∧
    (∀ x y : V, x ≠ y → edge C .lt x y ∨ edge C .lt y x)

/-- The constructed counterexample K is a subclass of the
natural ambient class of finite ordered relational structures. -/
theorem finitePairedClass_subset_orderedAmbient
    {V : Type} (C : RelStructure Lang V)
    (hC : finitePairedClass C) :
    orderedAmbientClass C :=
  ⟨hC.1, hC.2.lt_irrefl, hC.2.lt_trans, hC.2.lt_total⟩

/-- The distinguished strict total binary order witnesses ordinary
irreducibility of every member of the ambient class. -/
theorem orderedAmbient_irreducible
    {V : Type} (C : RelStructure Lang V)
    (hC : orderedAmbientClass C) :
    C.Irreducible := by
  intro x y hxy
  rcases hC.2.2.2 x y hxy with hlt | hgt
  · refine ⟨.lt, ![x, y], 0, 1, ?_, rfl, rfl⟩
    exact hlt
  · refine ⟨.lt, ![y, x], 1, 0, ?_, rfl, rfl⟩
    exact hgt

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
