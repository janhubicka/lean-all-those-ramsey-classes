import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceAge
import AllThoseRamseyClasses.Lifts.FiniteFunctionalExpansionFibres

/-!
# Nonempty finite fibres of the finite-family maximal induced trace age

The hereditary maximal induced trace class is a genuine *precompact
expansion* over every FINITE forbidden-free OLD structure:

* Existence: finite positive-profile maximization yields a finite
  forbidden-free witness W maximal along the original carrier A.
  Taking its FULL induced component-tag trace on A gives an age
  member with the EXACT old functional shadow A.
* Precompactness: the added component-tag signature is FINITE for
  a finite named forbidden family, and each old finite carrier has
  only finitely many total interpretations of those new relations.
  The maximal-trace class is a subtype of that finite fibre.

This does not imply the Ramsey property, joint embedding, or the
printed 2019 regular-infinite-family precompactness theorem.
Nothing in the native partial-function fibres is altered.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every finite structure avoiding the named weak-EHN forbidden
family is the literal old functional shadow of an actual member
of the hereditary finite maximal-component-trace class. -/
theorem finiteNamedMaximalTraceAge_exists_above
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {V : Type} [Finite V]
    (A : Structure L V)
    (hAvoid : AvoidsFiniteNamedEHN Family A) :
    ∃ (Y : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) V),
      FiniteNamedTraceShadow Family Y = A ∧
      IsFiniteNamedMaximalTrace Family Y := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let aId : Structure.Embedding A A := Structure.Embedding.id A
  obtain ⟨UW, W, hFiniteW, hAvoidW, e, hMax⟩ :=
    finiteNamed_exists_finite_maximal_extension
      Family aId hAvoid
  letI : Finite UW := hFiniteW
  let i : Structure.Embedding A W := e.comp aId
  exact ⟨finiteNamedCanonicalTrace Family i,
    finiteNamedCanonicalTrace_shadow Family i,
    finiteNamedCanonicalTrace_mem_age Family i hAvoidW hMax⟩

/-- All actual maximal induced traces of ONE fixed finite native
structure A. The outer subtype requires membership in the
verified finite maximal-trace age. The inner subtype fixes the
ENTIRE old relation/function shadow, not merely the carrier. -/
noncomputable def FiniteNamedMaximalTraceFibre
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {V : Type} (A : Structure L V) :=
  {Y : FixedFunctionalShadowExpansions L Family.ComponentTag
      (fun tag => tag.width Family) A //
    IsFiniteNamedMaximalTrace Family Y.1}

/-- The maximal lifted age has FINITELY MANY expanded structures
over each fixed finite forbidden-free old carrier (in fact for
any fixed finite old structure, whether forbidden-free or not). -/
theorem finiteNamedMaximalTraceFibre_finite
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {V : Type} [Finite V] (A : Structure L V) :
    Finite (FiniteNamedMaximalTraceFibre Family A) := by
  letI : Finite
      (FixedFunctionalShadowExpansions L Family.ComponentTag
        (fun tag => tag.width Family) A) :=
    fixedFunctionalShadowExpansions_finite
      L Family.ComponentTag (fun tag => tag.width Family) A
  unfold FiniteNamedMaximalTraceFibre
  infer_instance

/-- Each finite forbidden-free shadow has a NONEMPTY finite fibre
of genuinely maximal induced traces. Hence this is a literal
finite-fibre expansion, not a merely conditional candidate
relation signature. -/
theorem finiteNamedMaximalTraceFibre_nonempty
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {V : Type} [Finite V] (A : Structure L V)
    (hAvoid : AvoidsFiniteNamedEHN Family A) :
    Nonempty (FiniteNamedMaximalTraceFibre Family A) := by
  obtain ⟨Y, hShadow, hAge⟩ :=
    finiteNamedMaximalTraceAge_exists_above Family A hAvoid
  exact ⟨⟨⟨Y, hShadow⟩, hAge⟩⟩

end AllThoseRamseyClasses.Lifts
