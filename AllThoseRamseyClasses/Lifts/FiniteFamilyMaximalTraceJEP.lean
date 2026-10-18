import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceTransfer

/-!
# Joint embedding transfers to the hereditary maximal-trace age

Strong AP of the new finite-family maximal-trace age does NOT by
itself give JEP when the forbidden sources are disconnected: the
base forbidden-free class may have incompatible finite members.

This module proves the precise reusable conditional implication:
if finite forbidden-free OLD functional structures have JEP by
FULL embeddings, then their maximal induced component-tag traces
have JEP by FULL expanded embeddings.

Proof uses native witness embeddings to find one finite allowed
common structure C, extends C to a finite allowed witness M
maximal along C, and transfers the two old full embeddings into the
induced canonical trace on C. The tag reflection on the original
two expanded members follows from their witness maximality.

No old/new-language categorical machinery or hidden free-amalgam
assumption; no claim that the native forbidden-free class always
has JEP. The full original 2019 regular-family theorem is separate.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Conditional FULL joint embedding property for finite native
functional structures avoiding a named forbidden family. Forbidding
disconnected sources may prevent this property. -/
def FiniteNamedNativeFiniteJEP
    (Family : FiniteNamedFunctionalSources.{u,0} L) : Prop :=
  ∀ {UA UB : Type}
    (A : Structure L UA) (B : Structure L UB),
    Finite UA → Finite UB →
    AvoidsFiniteNamedEHN Family A →
    AvoidsFiniteNamedEHN Family B →
    ∃ (UC : Type) (C : Structure L UC),
      Finite UC ∧ AvoidsFiniteNamedEHN Family C ∧
      ∃ (_eA : Structure.Embedding A C)
        (_eB : Structure.Embedding B C), True

/-- Every finite maximal component-trace class whose native finite
forbidden-free shadows admit FULL JEP also has FULL JEP. This
statement is deliberately conditional on the native JEP hypothesis:
strong amalgamation alone is not a substitute. -/
theorem finiteNamedMaximalTraceAge_JEP_of_nativeJEP
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (hJEP : FiniteNamedNativeFiniteJEP Family)
    {VY VZ : Type}
    (Y : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VY)
    (Z : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VZ)
    (hY : IsFiniteNamedMaximalTrace Family Y)
    (hZ : IsFiniteNamedMaximalTrace Family Z) :
    ∃ (VT : Type)
      (T : Structure
        (functionalLiftLanguageBig L Family.ComponentTag
          (fun tag => tag.width Family)) VT),
      IsFiniteNamedMaximalTrace Family T ∧
      ∃ (_jY : Structure.Embedding Y T)
        (_jZ : Structure.Embedding Z T), True := by
  classical
  obtain ⟨_hFinY, UWY, WY, hFinWY, hAvoidWY,
    iY, hMaxY, hRelY⟩ := hY
  obtain ⟨_hFinZ, UWZ, WZ, hFinWZ, hAvoidWZ,
    iZ, hMaxZ, hRelZ⟩ := hZ
  obtain ⟨VD, D, hFinD, hAvoidD, eWY, eWZ, _⟩ :=
    hJEP WY WZ hFinWY hFinWZ hAvoidWY hAvoidWZ
  letI : Finite VD := hFinD
  letI : Fintype VD := Fintype.ofFinite VD
  let dId : Structure.Embedding D D := Structure.Embedding.id D
  obtain ⟨UM, M, hFinM, hAvoidM, eDM, hMaxD⟩ :=
    finiteNamed_exists_finite_maximal_extension Family dId hAvoidD
  letI : Finite UM := hFinM
  let rootD : Structure.Embedding D M := eDM.comp dId
  have hMember : IsFiniteNamedMaximalTrace Family
      (finiteNamedCanonicalTrace Family rootD) :=
    finiteNamedCanonicalTrace_mem_age Family rootD hAvoidM hMaxD
  let baseY : Structure.Embedding
      (FiniteNamedTraceShadow Family Y) D := eWY.comp iY
  let baseZ : Structure.Embedding
      (FiniteNamedTraceShadow Family Z) D := eWZ.comp iZ
  let jY : Structure.Embedding Y
      (finiteNamedCanonicalTrace Family rootD) :=
    finiteNamedMaximalTrace_embedding_into_allowed_trace
      Family Y WY iY hMaxY hRelY D baseY M
      ⟨hFinM, hAvoidM⟩ rootD (eDM.comp eWY)
      (by intro y; rfl)
  let jZ : Structure.Embedding Z
      (finiteNamedCanonicalTrace Family rootD) :=
    finiteNamedMaximalTrace_embedding_into_allowed_trace
      Family Z WZ iZ hMaxZ hRelZ D baseZ M
      ⟨hFinM, hAvoidM⟩ rootD (eDM.comp eWZ)
      (by intro z; rfl)
  exact ⟨VD, finiteNamedCanonicalTrace Family rootD,
    hMember, jY, jZ, True.intro⟩

end AllThoseRamseyClasses.Lifts
