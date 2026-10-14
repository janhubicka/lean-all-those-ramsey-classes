import AllThoseRamseyClasses.Published.Definitions
import AllThoseRamseyClasses.Published.InducedClosedLogicalDirection
import AllThoseRamseyClasses.Published.InducedClosed2019MainContract
import AllThoseRamseyClasses.Published.InducedClosed2019ClassBridge
import AllThoseRamseyClasses.Published.InducedClosed2019HereditaryBridge
import AllThoseRamseyClasses.Published.InducedClosed2019UnrestrictedInitial
import AllThoseRamseyClasses.Published.InducedClosed2019CutoffThree
import AllThoseRamseyClasses.Published.Coordinated2019ProfileSparseWitness
import PartiteConstruction.Ramsey.ClosureUSize2019
import PartiteConstruction.Ramsey.ClosureSemiClosed2019
import PartiteConstruction.Ramsey.ClosureClosedLocalFiniteness
import PartiteConstruction.Ramsey.ClosureFreeAmalgamCompletion
import PartiteConstruction.Ramsey.CopywiseRamseyTransfer
import PartiteConstruction.Ramsey.AllThosePartialFiniteModels

/-!
# Researcher-facing API for the validated 2019 Ramsey results

Import this module for the coordinated corrected *relational*
multiamalgamation theorem, its exact paper-style class and
local-completion predicates, the 2019 closure definitions, the
unrestricted initial Picture and fixed-cutoff corollaries, and the
separately verified free partial-function ordered Ramsey theorem.

The printed literal 2019 main theorem is refuted by a checked
counterexample. The theorem exported here has the TWO explicitly
coordinated corrections:

* protected map tests are simultaneously intrinsically U-closed
  and U-irreducible;
* (4b) tests membership of precisely those same induced structures.

The original exact weak induced subsets of size at most the
preselected n(B,C0) are still all tested in (4c). Do not replace them
with a closure hull. The 2019 native rank-increment Lemma 2.30 is not
certified by this alternative profile/sparsening proof.

This file intentionally does NOT aggregate unfinished application
Ramsey claims. Application *components* have separate imports and
scoped certificates; see README.md and docs/public-api-reference.md.
-/

namespace AllThoseRamseyClasses.Published

universe u v
variable {L : StructuralRamsey.RelLanguage.{u}}

/-- The repaired Theorem 2.18 packaged exactly as the pre-existing
paper-style target proposition, so a researcher can use either this
entry point or `coordinated2019_ramsey_by_profile_sparsening`.

Unlike `coordinated2019_target_of_abstract_target`, this theorem
has NO abstract Ramsey-theorem hypothesis: it invokes the actually
constructed unrestricted profile-sparsening witness. -/
theorem coordinated2019_theorem218 :
    Coordinated2019Theorem218Target.{u,v} (L := L) := by
  intro R K rules hR hRIrred hK
  exact coordinated2019_ramsey_by_profile_sparsening R K rules hR hRIrred hK

end AllThoseRamseyClasses.Published
