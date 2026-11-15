import AllThoseRamseyClasses.Lifts.EHNOriginalFullTestTransportFirewall
import AllThoseRamseyClasses.Lifts.EHNFiveCycleTransportFailure

/-!
# Track D adversarial regression: local test transport is genuinely
weaker than any full old-source embedding

Use the already kernel-verified genuine ORIGINAL native EHN map
from the five-cycle to a three-vertex target with a binary graph
relation and an extra ternary tuple.

The map is noninjective and the entire full five-cycle does NOT
embed into the target (five source vertices versus three target
vertices), yet by the EHN full-test clause EVERY original
irreducible source test is transported with its prescribed
weak-map coordinates.

This is a positive explicit countercheck against confusing the
full-test-transport condition in source surgery with a global
full native embedding. It is NOT a counterexample to the
maximal-common-lift strong amalgamation statement: the target
here is not the required full free amalgam of maximal witnesses.
-/

namespace AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Lifts
open AllThoseRamseyClasses.Lifts.RootCollisionFiveCycle

/-- TRUE genuine EHN map can transport every original full
irreducible source test without being globally injective. -/
theorem cycle5_noninjective_fullIrreducibleTestTransport :
    TransportsOriginalFullIrreducibleTests
      cycle5 triangleExtraTernary weakColor ∧
    ¬ Function.Injective weakColor := by
  have hTest :=
    (nativeEHN_iff_weak_and_transportsFullIrreducibleTests
      cycle5 triangleExtraTernary weakColor).1
        weakColor_nativeEHN
  exact ⟨hTest.2, weakColor_not_injective⟩

/-- Strong regression: the original C5-to-triangle EHN map
transports all full irreducible source tests although not
even ONE full embedding of the whole C5 into the target
exists. The new source-surgery transport condition therefore
does NOT silently assert a full global source image. -/
theorem cycle5_fullTestTransport_without_fullOldEmbedding :
    TransportsOriginalFullIrreducibleTests
      cycle5 triangleExtraTernary weakColor ∧
    ¬ Nonempty (Structure.Embedding cycle5 triangleExtraTernary) := by
  exact ⟨cycle5_noninjective_fullIrreducibleTestTransport.1,
    no_native_full_C5_embedding⟩

end AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap
