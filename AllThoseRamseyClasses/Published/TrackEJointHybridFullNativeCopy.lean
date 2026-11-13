import AllThoseRamseyClasses.Published.TrackEJointHybridNativeClosedIff
import AllThoseRamseyClasses.Published.TrackEFullCopyPartitePullback
import AllThoseRamseyClasses.Published.TrackEOldSplitHybridCanonical
import AllThoseRamseyClasses.Published.TrackEJointHybridExactInduce

/-!
# Track E2: arbitrary FULL native copies lift into canonical JOINT hybrid tests

A 2019 finite-family ambient irreducible test is an arbitrary
genuinely native Structure E and FULL native embedding e:E↪A.
It need not be supplied with its own vertex part map.

The verified full-copy pullback gives E the precise actual parts
part_A ∘ e. Every original relation and entire multivalued
function fibre is preserved by this FULL map. Then the verified
hybrid functor and the verified JOINT full-root tag functor give
one FULL relational embedding of the canonical tagged E into the
canonical tagged A, with EXACT underlying vertex function e.

If E is genuinely native irreducible and all primitive function
input arities are positive, the newly proved canonical joint
closed-cover criterion implies this FULL tagged E source is
intrinsically U-irreducible for the actual combined split and
complete-original-mask closure rules.

This removes a separate part-labelling or source-test lookup
oracle from the canonical test-eligibility problem. It does NOT
claim that the image of E in an arbitrary NONCANONICAL final
sparse picture automatically has the canonical induced tags:
the missing comparison remains explicit. In particular it does
not upgrade a weak source-defined map to a full embedding or
replace the exact test by a generated closure hull.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- One arbitrary FULL native test e:E↪A induces a FULL relational
embedding of the corresponding canonical JOINT split/mask tagged
presentations on EXACTLY the same vertices and vertex map e.
Part labels on E are pulled back from the actual ambient A. -/
noncomputable def fullNativeCopy_jointHybridEmbedding
    {VA VE : Type w}
    (A : FunctionalPartite.System L Parts VA)
    (E : Structure L VE)
    (e : Structure.Embedding E A.toStructure) :
    RelStructure.Embedding
      (splitMaskJointRootExpansion
        (systemOnFullCopy A E e).splitMaskHybrid)
      (splitMaskJointRootExpansion A.splitMaskHybrid) :=
  (systemEmbedding_splitMaskHybrid
    (systemOnFullCopy_embedding A E e)).splitMaskJointRoot

/-- A FULL native test's genuine original underlying vertex map is
unchanged by either canonical hybrid encoding or full-root tagging. -/
@[simp] theorem fullNativeCopy_jointHybridEmbedding_apply
    {VA VE : Type w}
    (A : FunctionalPartite.System L Parts VA)
    (E : Structure L VE)
    (e : Structure.Embedding E A.toStructure)
    (x : VE) :
    fullNativeCopy_jointHybridEmbedding A E e x = e x := rfl

/-- Every arbitrary finite FULL irreducible native test embedded in
a genuine native partite ambient System has an intrinsically
U-irreducible canonical JOINT tagged representation, with its
part labels literally pulled back through the provided FULL map.

The test does not need to be presented as a primitive partite
System beforehand. The conclusion is intrinsic relative to the
combined full-hybrid-root closure rules, NOT Gaifman completeness. -/
theorem fullNativeIrreducibleCopy_jointHybrid_uIrreducible
    {VA VE : Type w} [Finite VE]
    (A : FunctionalPartite.System L Parts VA)
    (E : Structure L VE)
    (e : Structure.Embedding E A.toStructure)
    (hPos : L.PositiveFuncArity)
    (hIrred : E.Irreducible) :
    IsUIrreducible (L.splitMaskJointClosureRules Parts)
      (splitMaskJointRootExpansion
        (systemOnFullCopy A E e).splitMaskHybrid) := by
  exact nativeIrreducible_canonicalJointHybrid_uIrreducible
    (systemOnFullCopy A E e) hPos hIrred

end AllThoseRamseyClasses.Published
