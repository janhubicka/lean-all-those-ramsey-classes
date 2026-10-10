import AllThoseRamseyClasses.Published.OrderedAmbient
import Mathlib.Order.RelClasses

/-!
# Recovering the external linear order of an ambient structure

An ambient 2019 (<,E,M)-structure has a strict total relation <.
Mathlib's linearOrderOfSTO reconstructs the corresponding bundled
LinearOrder. The equivalence between that order and the interpretation
of the named < symbol is the bridge to the already checked ordered
relational Ramsey theorem, where < is part of the language expansion.

No Ramsey-class conclusion is claimed by these order lemmas alone.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The original strict binary relation, using the SAME order
interpretation as the published class rather than introducing a
new independently chosen ordering. -/
noncomputable def ambientLinearOrder
    {V : Type} (C : RelStructure Lang V)
    (hC : orderedAmbientClass C) : LinearOrder V := by
  letI : IsStrictTotalOrder V (edge C .lt) := {
    trichotomous := by
      intro a b hnab hnba
      by_contra hne
      rcases hC.2.2.2 a b hne with hab | hba
      · exact hnab hab
      · exact hnba hba
    irrefl := hC.2.1
    trans := hC.2.2.1
  }
  letI : DecidableRel (edge C .lt) := Classical.decRel _
  exact linearOrderOfSTO (edge C .lt)

/-- The extracted order has EXACTLY the published binary < relation.
There is no order expansion and no new choice of order. -/
theorem ambientLinearOrder_lt_iff
    {V : Type} (C : RelStructure Lang V)
    (hC : orderedAmbientClass C)
    (x y : V) :
    @LT.lt V (ambientLinearOrder C hC).toLT x y ↔
      edge C .lt x y := by
  rfl

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
