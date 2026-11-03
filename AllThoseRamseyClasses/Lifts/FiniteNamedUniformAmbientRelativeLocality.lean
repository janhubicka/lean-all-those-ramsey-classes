import AllThoseRamseyClasses.Lifts.FiniteFamilyAmbientRelativeLocality
import AllThoseRamseyClasses.Lifts.FiniteNamedFamilySourceSizeCutoff

/-!
# Track E2: unconditional exact finite-family weak-locality criterion

The finite family itself supplies a fixed finite numeric cutoff:
the total size of the disjoint union of all its named source carriers.
This need not be optimal, but dominates every forbidden source,
including when the named family is empty and the native functional
signature has arbitrary arities.

By the independently verified ambient-relative locality theorem,
a finite native candidate D avoids all named forbidden EHN sources
IF AND ONLY IF each literal weak-induced subset S of at most this
fixed cutoff has a finite forbidden-free ambient-relative completion.

No user-supplied local bound, source image injection, function closure
of a test set, or extra class amalgamation hypotheses are required.
Weak completion protects only full ambient irreducible tests and
whole nonempty fibres whose entire original output remains in S.

This closes the finite-family NUMERICAL locality criterion E2.
It does not construct a sparse Ramsey witness C satisfying that
criterion and an ordered Ramsey arrow simultaneously.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Exact local characterization with ONE family-defined cutoff.
This statement holds for any finite candidate D, regardless of
whether D is a member of the finite-family forbidden-free class.

The criterion is genuinely equivalent, not only sufficient: if
D avoids the forbidden family, D itself provides every
ambient-relative weak test completion. -/
theorem avoidsFiniteNamedEHN_iff_uniformAmbientRelativeWeakCompletions
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VD : Type} [Finite VD]
    (D : Structure L VD) :
    AvoidsFiniteNamedEHN Family D ↔
      FiniteNamedAmbientRelativeWeakCompletions
        Family D (finiteNamedTotalForbiddenVertexCutoff Family) :=
  avoidsFiniteNamedEHN_iff_ambientRelativeWeakCompletions
    Family D (finiteNamedTotalForbiddenVertexCutoff Family)
    (finiteNamedSource_card_le_totalCutoff Family)

/-- Direct implication from the fixed finite-family local tests to
native forbidden avoidance, without restating any cardinality
bound in the application theorem. -/
theorem avoidsFiniteNamedEHN_of_uniformAmbientRelativeWeakCompletions
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VD : Type} [Finite VD]
    (D : Structure L VD)
    (hLocal : FiniteNamedAmbientRelativeWeakCompletions
      Family D (finiteNamedTotalForbiddenVertexCutoff Family)) :
    AvoidsFiniteNamedEHN Family D :=
  (avoidsFiniteNamedEHN_iff_uniformAmbientRelativeWeakCompletions
    Family D).mpr hLocal

end AllThoseRamseyClasses.Lifts
