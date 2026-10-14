import AllThoseRamseyClasses.Published.OrderedAmbientRamsey

/-!
# Original 2019 application: finite ordered posets, class interface

We use the already checked SAME NAMED ordered ambient language
(<, E, M), interpreting E as the reflexive partial order and M
as the empty auxiliary relation. The empty M-relation is inert:
this is definitionally the two-binary-relation ordered-poset
application once the redundant empty symbol is forgotten.

This file states and verifies the nontrivial class membership and
ambient irreducibility interface without claiming yet to verify
strong amalgamation or the corrected exact weak local-completion
condition. Those two obligations must be discharged to apply the
general corrected coordinated multiamalgamation theorem.
-/

namespace AllThoseRamseyClasses.Applications.OrderedPosets

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- A (reflexive) finite partial order E with arbitrary vertex order
< that extends E, plus an inert empty M relation. -/
def orderedPosetClass : StructureClass (L := Lang) :=
  fun {V} (C : RelStructure Lang V) =>
    orderedAmbientClass C ∧
    (∀ x : V, edge C .equiv x x) ∧
    (∀ x y z : V, edge C .equiv x y →
      edge C .equiv y z → edge C .equiv x z) ∧
    (∀ x y : V, edge C .equiv x y →
      edge C .equiv y x → x = y) ∧
    (∀ x y : V, x ≠ y → edge C .equiv x y →
      edge C .lt x y) ∧
    (∀ x y : V, ¬ edge C .mate x y)

/-- The candidate ordered-poset K belongs to the verified general
ordered-relational ambient Ramsey class R, with NO extra order. -/
theorem orderedPosetClass_subset_ambient
    {V : Type} (C : RelStructure Lang V)
    (hC : orderedPosetClass C) : orderedAmbientClass C :=
  hC.1

/-- Finite carrier is inherited from the ambient class. -/
theorem orderedPosetClass_finite
    {V : Type} (C : RelStructure Lang V)
    (hC : orderedPosetClass C) : Finite V :=
  hC.1.1

/-- Every candidate ordered-poset member is ordinarily irreducible,
because its ORIGINAL named order compares every distinct pair. -/
theorem orderedPosetClass_irreducible
    {V : Type} (C : RelStructure Lang V)
    (hC : orderedPosetClass C) : C.Irreducible :=
  orderedAmbient_irreducible C hC.1

/-- A strict E-comparison is always compatible with the original
named vertex order. There is no convexity/admissibility restriction. -/
theorem orderedPosetClass_order_extension
    {V : Type} (C : RelStructure Lang V)
    (hC : orderedPosetClass C)
    (x y : V) (hne : x ≠ y)
    (hp : edge C .equiv x y) :
    edge C .lt x y :=
  hC.2.2.2.2.1 x y hne hp

/-- R is Ramsey by the already CI-checked exact named-order bridge.
This is an imported result, not an added assumption. -/
theorem orderedPosetAmbient_isRamsey :
    FiniteRamseyClass orderedAmbientClass :=
  orderedAmbient_isRamsey

end AllThoseRamseyClasses.Applications.OrderedPosets
