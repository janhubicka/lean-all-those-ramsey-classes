import AllThoseRamseyClasses.Published.TrackENativeIrreducibleTaggedU
import AllThoseRamseyClasses.Published.TrackEOutputPartSplitIrreducibility
import AllThoseRamseyClasses.Published.TrackEFullCopyPartitePullback
import PartiteConstruction.Functional.OutputPartSingletonUClosedBridge

/-!
# Track E2: actual multivalued partite full tests have U-irreducible split tags

An arbitrary full native irreducible test E embedded into a partite
ambient A need not come with its own part labels. The merged full-copy
pullback constructs those labels literally from the given full map.
Canonical output-part splitting turns all the multivalued function
fibres into per-output-part singleton functions without changing
the carrier or full embedding.

The closed-cover theorem #1016 and the canonical singleton
U-irreducibility theorem #1019 then imply that the canonical 2019
full-root tagged graph of the split test is U-IRREDUCIBLE. This is
the exact strengthened native U-test property required to apply the
corrected induced-closed 2019 completion-map protection clause.

It is NOT ordinary relational irreducibility of the pattern graph,
and is not an identification of the canonical tagged test with an
arbitrary noncanonical final sparse tagged picture. It also does
not supply the split local completion map or the ordered E2 control.

Only POSITIVE original function arities are included. Nullary
functions require their separate root reduction.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v}

/-- A native full irreducible genuine partite System becomes an
intrinsically U-irreducible canonical singleton-output-part
tagged graph, with SAME vertex carrier and part map. -/
theorem nativePartiteIrreducible_splitPatternTag_uIrreducible
    {V : Type w} [Finite V]
    (A : FunctionalPartite.System L Parts V)
    (hPos : L.PositiveFuncArity)
    (hIrr : A.toStructure.Irreducible) :
    IsUIrreducible
      (L.outputPartIndexed Parts).patternClosureRules
      (patternTagExpansion
        A.splitOutputParts.toStructure.patternGraph) := by
  exact nativeIrreducible_canonicalSingletonTag_uIrreducible
    A.splitOutputParts.toStructure
    hPos.outputPartIndexed
    A.splitOutputParts_singletonValued
    (nativeIrreducible_splitOutputParts A hIrr)

/-- Every arbitrary FULL native irreducible test E embedded in
a genuine partite ambient System A inherits an exact partite
source presentation; its singletonized canonical 2019 full-root
tagged presentation is intrinsically U-irreducible.

The full source E and its part labels are not assumed separately:
they are reconstructed on the literal carrier E from the given
full embedding e:E↪A. No weak-test closure hull is taken. -/
theorem fullNativeIrreducibleCopy_splitPatternTag_uIrreducible
    {VA VE : Type w} [Finite VE]
    (A : FunctionalPartite.System L Parts VA)
    (E : Structure L VE)
    (e : Structure.Embedding E A.toStructure)
    (hPos : L.PositiveFuncArity)
    (hIrr : E.Irreducible) :
    IsUIrreducible
      (L.outputPartIndexed Parts).patternClosureRules
      (patternTagExpansion
        (systemOnFullCopy A E e).splitOutputParts.toStructure.patternGraph) := by
  exact nativePartiteIrreducible_splitPatternTag_uIrreducible
    (systemOnFullCopy A E e) hPos hIrr

end AllThoseRamseyClasses.Published
