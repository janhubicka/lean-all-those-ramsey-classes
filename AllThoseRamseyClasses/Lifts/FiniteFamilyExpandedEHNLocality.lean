import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceAge
import AllThoseRamseyClasses.Lifts.FunctionalShadowEHN
import AllThoseRamseyClasses.Lifts.FiniteFamilyAmbientRelativeEHNPullback
import AllThoseRamseyClasses.Lifts.FiniteNamedUniformAmbientRelativeLocality

/-!
# Track E2: exact weak-test locality along EXPANDED functional partite maps

The actual EHN partite construction produces maps in the full
finite-family component-tag language, while forbidden family
avoidance and local tests refer to the original native functional
shadow. Two verified technical bridges now compose:

* An expanded EHN homomorphism-embedding is EHN on its literal
  native functional shadow, preserving ALL original set-valued
  function fibres on full irreducible tests.
* An EHN map pulls bounded ambient-relative weak completion
  backwards on the EXACT image of every weak vertex test,
  without function-closure hulls or spurious clipped
  irreducibles.

Thus any expanded partite stage with an EHN projection into
a locally completable expanded base inherits the same bound
on native weak-test completions. At the fixed source-size bound,
it also inherits forbidden-family avoidance of its native
shadow. This is a genuine native statement from an actual
expanded EHN projection; no global full embedding or
identification of function domains is presumed.

It is the small-image side of E2. The missing **rank increment**
for mixed weak tests is NOT proved here. In particular, the
ambient unrestricted Ramsey control need not satisfy any
local-completion bound, so this theorem alone does not
construct a sparse Ramsey witness.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Any EHN projection in the finite named component-tag language
pulls native ambient-relative weak-test completions backwards,
at the SAME exact vertex bound n. In particular no closure
hull or global fibre-surjectivity of the projection is used. -/
theorem finiteNamedLocalCompletions_of_expandedEHNProjection
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VC VD : Type} [Finite VC] [Finite VD]
    {C : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VC}
    {D : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VD}
    {p : VC → VD}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (n : ℕ)
    (hD : FiniteNamedAmbientRelativeWeakCompletions
      Family (FiniteNamedTraceShadow Family D) n) :
    FiniteNamedAmbientRelativeWeakCompletions
      Family (FiniteNamedTraceShadow Family C) n := by
  exact finiteNamedAmbientRelativeWeakCompletions_of_EHNProjection
    Family
    (functionalEHN_shadowBig L Family.ComponentTag
      (fun tag => tag.width Family) hp)
    n hD

/-- At the fixed, explicitly constructed finite source-size cutoff,
an EXPANDED EHN projection from C into D transfers forbidden-family
avoidance from the literal native shadow of D to that of C.

This does not claim avoidance of arbitrary ambient Ramsey controls,
nor does it need a full map from C to D. -/
theorem finiteNamedShadow_avoids_of_expandedEHNProjection
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VC VD : Type} [Finite VC] [Finite VD]
    {C : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VC}
    {D : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VD}
    {p : VC → VD}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (hD : AvoidsFiniteNamedEHN
      Family (FiniteNamedTraceShadow Family D)) :
    AvoidsFiniteNamedEHN
      Family (FiniteNamedTraceShadow Family C) := by
  have hLocalD :
      FiniteNamedAmbientRelativeWeakCompletions
        Family (FiniteNamedTraceShadow Family D)
        (finiteNamedTotalForbiddenVertexCutoff Family) :=
    (avoidsFiniteNamedEHN_iff_uniformAmbientRelativeWeakCompletions
      Family (FiniteNamedTraceShadow Family D)).mp hD
  have hLocalC :=
    finiteNamedLocalCompletions_of_expandedEHNProjection
      Family hp (finiteNamedTotalForbiddenVertexCutoff Family)
      hLocalD
  exact avoidsFiniteNamedEHN_of_uniformAmbientRelativeWeakCompletions
    Family (FiniteNamedTraceShadow Family C) hLocalC

end AllThoseRamseyClasses.Lifts
