import AllThoseRamseyClasses.Published.PairedStrongAmalgamation
import AllThoseRamseyClasses.Published.Corrected4bLocalCounterexample
import AllThoseRamseyClasses.Published.LiteralCounterexampleAssembly

/-!
# Conditional-on-base-branch finished counterexamples to Theorem 2.18

These tiny logical consequences depend on the ACTUAL finite strong
amalgamation declaration established in the parent PR. If parent CI
has not succeeded, NO green certification is available here.

The first declaration refutes the printed literal 2019
multiamalgamation theorem. The second refutes the proposed
one-clause (4b)-only version retaining the literal 2019 maps.

This does NOT refute the coordinated closed-test map plus (4b)
repair, whose general positive Ramsey theorem remains open.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- The literal printed 2019 Theorem 2.18 fails for finite
ordered paired equivalences. Requires an actual strong-amalgam
proof in the parent import, never an assumed axiom. -/
theorem literalTheorem218_counterexample :
    ¬ AllThoseRamseyClasses.Published.LiteralTheorem218Target.{0,0}
        (L := Lang) := by
  intro hPublished
  exact (literalTheorem218_implies_not_pairedStrong hPublished)
    finitePairedClass_strong_amalgamation

/-- The (4b)-ONLY correction also fails: retaining original
Definition 2.15 maps gives a trivial cutoff |C0|+1. -/
theorem corrected4bOnlyTheorem218_counterexample :
    ¬ AllThoseRamseyClasses.Published.CorrectedTheorem218Target.{0,0}
        (L := Lang) := by
  intro hCorrected
  exact (correctedTheorem218_implies_not_pairedStrong hCorrected)
    finitePairedClass_strong_amalgamation

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
