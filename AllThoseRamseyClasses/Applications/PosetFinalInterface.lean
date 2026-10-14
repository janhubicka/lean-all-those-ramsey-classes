import AllThoseRamseyClasses.PublicAPI
import AllThoseRamseyClasses.Applications.PosetStrongAmalgamation
import AllThoseRamseyClasses.Applications.OrderedPosetHereditary

/-!
# The exact remaining hypothesis for the ordered-poset Ramsey application

The source-faithful relational model uses the SAME named binary order,
partial-order and empty auxiliary symbols as the 2019 manuscript.
The ordinary order symbol `.lt` represents STRICT order, while
`.equiv` represents the REFLEXIVE partial order.

This interface packages the exact local-completion axiom as the one
remaining *input to this module*, using its original weak-test cardinal
bound `n(B,C0) = Nat.card Y` on the ORIGINAL control C0.
The later PosetRamseyTheorem module proves that input unconditionally.

The theorems in this file discharge ALL OTHER fields explicitly,
and conclude the Ramsey theorem conditionally on exactly this
remaining local-completion statement. They do NOT assume an arbitrary
Ramsey theorem or a general sparse witness as a hidden hypothesis.

This file alone is a conditional interface/blueprint; the completed
Ramsey-class application is in PosetRamseyTheorem.
-/

namespace AllThoseRamseyClasses.Applications.OrderedPosets

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published
open AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- The only remaining 2019 class axiom, with a *concrete* local
cutoff equal to the cardinality of the originally chosen ambient
control. Each test is an original weak induced subset, not a
generated closure. -/
def OrderedPosetExactLocalAtControlCard : Prop :=
  ∀ {X Y : Type} [Finite X] [Finite Y]
    (B : RelStructure Lang X) (C0 : RelStructure Lang Y),
    orderedPosetClass B → orderedAmbientClass C0 →
    InducedClosedULocalCompletionAt
      orderedPosetClass (∅ : ClosureDescription Lang)
      B C0 (Nat.card Y)

/-- Subclass, finite carriers, empty U-closedness, ordinary induced
heredity, actual finite strong amalgamation and isomorphism closure:
all hypotheses are proved, not postulated. Only the fixed-cutoff
local-completion property remains a named input. -/
theorem orderedPoset_coordinatedClass_of_exactLocal
    (hLocal : OrderedPosetExactLocalAtControlCard) :
    IsCoordinated2019MultiamalgamationClass
      orderedAmbientClass orderedPosetClass
      (∅ : ClosureDescription Lang) := by
  refine ⟨{
    subset := ?_
    finite := ?_
    closed := ?_
    hereditary := ?_
    strong := orderedPosetClass_strongAmalgamation
    localCompletion := ?_
  }, orderedPosetClass_isomorphismClosed⟩
  · intro X A hA
    exact orderedPosetClass_subset_ambient A hA
  · intro X A hA
    exact orderedPosetClass_finite A hA
  · intro X A hA rule hrule
    simp at hrule
  · intro X A hA S _
    exact orderedPosetClass_hereditary hA (inclusion A S)
  · intro X Y hFiniteX hFiniteY B C0 hB hC0
    exact ⟨Nat.card Y, hLocal B C0 hB hC0⟩

/-- The 2019 application reduces to ONE exact local-completion
statement. This is a *conditional* Ramsey theorem with its
remaining hypothesis explicit, not the completed poset corollary. -/
theorem orderedPoset_ramsey_of_exactLocal
    (hLocal : OrderedPosetExactLocalAtControlCard) :
    FiniteRamseyClass orderedPosetClass := by
  apply coordinated2019_ramsey_by_profile_sparsening
    orderedAmbientClass orderedPosetClass
    (∅ : ClosureDescription Lang)
    orderedPosetAmbient_isRamsey
  · intro X C hC
    exact orderedAmbient_irreducible C hC
  · exact orderedPoset_coordinatedClass_of_exactLocal hLocal

end AllThoseRamseyClasses.Applications.OrderedPosets
