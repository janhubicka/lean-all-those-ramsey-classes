import AllThoseRamseyClasses.Published.MatchingClosure
import PartiteConstruction.Iterated.FreeAmalgam
import PartiteConstruction.Ramsey.ClosureFreeAmalgamCompletion

/-!
# Matching-closure part of the finite strong-amalgamation construction

The general relational free amalgam is not in our K because its
equivalence relation may fail transitivity and its order may be
incomplete across sides. Nevertheless its M-relation is a full
closure relation with exactly one output above each singleton root.
This is a genuine verified prerequisite for the final strong
amalgamation: both the E-completion and order-completion stages
must preserve this matching relation unchanged.

No strong-amalgamation claim is made in this module.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

universe v
variable {H E F : Type v}

/-- A concrete FREE relational amalgam of members of our class
remains U-closed for the original M closure description.
This is not yet an amalgam in K, because E and < still need
their cross-side completion. -/
theorem freeAmalgam_matching_isUClosed
    (D : RelStructure Lang H)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (hD : pairedClass D) (hLeft : pairedClass Left)
    (hRight : pairedClass Right)
    (sL : Embedding D Left) (sR : Embedding D Right) :
    IsUClosed mateRules
      (FreeAmalgam.amalgam D Left Right sL sR) := by
  classical
  exact (FreeAmalgam.isFreeAmalgam D Left Right sL sR).isUClosed
    (pairedClass_isUClosed D hD)
    (pairedClass_isUClosed Left hLeft)
    (pairedClass_isUClosed Right hRight)

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
