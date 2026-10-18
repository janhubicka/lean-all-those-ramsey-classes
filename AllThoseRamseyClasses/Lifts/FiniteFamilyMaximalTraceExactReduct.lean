import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTracePrecompactness

/-!
# Exact reduct of the finite-family maximal-trace age

The existing existence and finite-fibre theorems prove that every finite
native forbidden-free shadow admits a finite maximal induced-component-trace
expansion. The converse is important: no member of the expanded age may
have a shadow containing an EHN forbidden witness.

The converse follows from a FULL embedding of the old shadow into its
finite forbidden-free maximizing witness. EHN homomorphism-embeddings
compose with full embeddings, including the complete old partial/function
value fibres and the irreducible-test embedding condition.

Consequently, on each finite named native carrier, the fibre of actual
maximal traces is nonempty IF AND ONLY IF the native shadow avoids the
finite family. This establishes the exact old-language reduct of this
finite-family homogenization, not merely an expansion existence theorem.

This does NOT establish the Ramsey property or the unrestricted regular
infinite-family theorem of the printed Section 3.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Avoidance of named EHN forbidden sources descends along arbitrary
FULL old-language embeddings. The source map need not be injective;
its irreducible tests are embedded by hypothesis. -/
theorem avoidsFiniteNamedEHN_of_embedding
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UA UB : Type}
    {A : Structure L UA} {B : Structure L UB}
    (e : Structure.Embedding A B)
    (hB : AvoidsFiniteNamedEHN Family B) :
    AvoidsFiniteNamedEHN Family A := by
  intro i f hf
  have hComp :
      (Family.source i).IsEHNHomomorphismEmbedding B (e ∘ f) :=
    e.isEHNHomomorphismEmbedding.comp hf
  exact (hB i (e ∘ f)) hComp

/-- Every actual member of the hereditary maximal-trace age has a
forbidden-free old shadow, not just a forbidden-free ambient witness.
This rules out spurious expanded objects in the proposed homogenization. -/
theorem finiteNamedMaximalTraceAge_shadow_avoids
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {V : Type}
    {Y : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) V}
    (hY : IsFiniteNamedMaximalTrace Family Y) :
    AvoidsFiniteNamedEHN Family (FiniteNamedTraceShadow Family Y) := by
  obtain ⟨_, UW, W, _, hAvoidW, iW, _, _⟩ := hY
  exact avoidsFiniteNamedEHN_of_embedding Family iW hAvoidW

/-- A finite native structure is the EXACT reduct of some hereditary
maximal canonical trace if and only if it avoids the named forbidden
EHN sources. Both directions retain all native function fibres. -/
theorem finiteNamedMaximalTraceAge_exact_reduct
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {V : Type} [Finite V]
    (A : Structure L V) :
    (∃ (Y : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) V),
      FiniteNamedTraceShadow Family Y = A ∧
      IsFiniteNamedMaximalTrace Family Y) ↔
    AvoidsFiniteNamedEHN Family A := by
  constructor
  · rintro ⟨Y, hShadow, hY⟩
    rw [← hShadow]
    exact finiteNamedMaximalTraceAge_shadow_avoids Family hY
  · exact finiteNamedMaximalTraceAge_exists_above Family A

/-- The genuine maximal-trace fibre above a finite native structure
is nonempty precisely when the shadow itself is forbidden-free.
Finiteness of every such fibre is already separately certified. -/
theorem finiteNamedMaximalTraceFibre_nonempty_iff_avoids
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {V : Type} [Finite V]
    (A : Structure L V) :
    Nonempty (FiniteNamedMaximalTraceFibre Family A) ↔
      AvoidsFiniteNamedEHN Family A := by
  constructor
  · rintro ⟨⟨⟨Y, hShadow⟩, hAge⟩⟩
    rw [← hShadow]
    exact finiteNamedMaximalTraceAge_shadow_avoids Family hAge
  · exact finiteNamedMaximalTraceFibre_nonempty Family A

end AllThoseRamseyClasses.Lifts
