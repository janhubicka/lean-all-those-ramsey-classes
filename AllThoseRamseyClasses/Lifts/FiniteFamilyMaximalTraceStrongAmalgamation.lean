import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceTransfer
import PartiteConstruction.Functional.FullFreeAmalgam

/-!
# Strong amalgamation of the HEREDITARY finite maximal-trace age

This closes the finite-family class-level strong-amalgamation bridge
for the alternative ALL-CLOSED-COMPONENT folded lift. Given two
finite maximal induced canonical traces A* and B* and full expanded
embeddings of the same X* into both:

1. Choose their FINITE forbidden-free maximizing witnesses WA, WB,
   whose native functional shadows contain A* and B* fully.
2. The two expanded embeddings of X* force exact agreement of ALL
   canonical tag predicates on the root embedded into WA and WB.
3. Construct the genuine FULL old functional free amalgam D of
   WA and WB over the old shadow of X*. Its forbidden-freeness follows
   from the verified weak-EHN component folding theorem.
4. Choose a finite forbidden-free extension M of D that is maximal
   along the ENTIRE D root, not necessarily along all of M.
5. The induced canonical tag TRACE of M on D belongs to our
   hereditary age. Both original expanded A*, B* fully embed into it:
   their source witnesses were maximal on their original displayed
   roots, so no new tag can appear there. Their images intersect
   exactly on X* by the actual old free-amalgam overlap law.

No presumption that expanded canonical lifts are hereditary or that
their amalgam is free in the added language. No auxiliary weak
embeddings are substituted for FULL function-preserving embeddings.

This proves strong AP of this alternative FINITE-family age. It does
not prove JEP (which may require a forbidden-free joint embedding
hypothesis), the Ramsey property, or the printed 2019 theorem for
arbitrary regular infinite forbidden families.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Strong amalgamation for finite **maximal induced component
traces**, over an arbitrary common FULL expanded substructure.
The membership hypothesis for the common root is unnecessary:
finiteness follows from its full embedding in a finite side.

The conclusion includes an ACTUAL finite lifted-age member and two
full expanded embeddings whose intersection is exactly the prescribed
common root, not merely a weak-source amalgam. -/
theorem finiteNamedMaximalTraceAge_strongAmalgamation
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VX VY VZ : Type}
    (X : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VX)
    (Y : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VY)
    (Z : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VZ)
    (hY : IsFiniteNamedMaximalTrace Family Y)
    (hZ : IsFiniteNamedMaximalTrace Family Z)
    (fY : Structure.Embedding X Y)
    (fZ : Structure.Embedding X Z) :
    ∃ (VT : Type)
      (T : Structure
        (functionalLiftLanguageBig L Family.ComponentTag
          (fun tag => tag.width Family)) VT),
      IsFiniteNamedMaximalTrace Family T ∧
      ∃ (jY : Structure.Embedding Y T)
        (jZ : Structure.Embedding Z T),
        ∀ y : VY, ∀ z : VZ,
          jY y = jZ z ↔
            ∃ x : VX, y = fY x ∧ z = fZ x := by
  classical
  obtain ⟨hFinY, UWY, WY, hFinWY, hAvoidWY,
    iY, hMaxY, hRelY⟩ := hY
  obtain ⟨hFinZ, UWZ, WZ, hFinWZ, hAvoidWZ,
    iZ, hMaxZ, hRelZ⟩ := hZ
  letI : Finite VY := hFinY
  letI : Finite VZ := hFinZ
  letI : Finite UWY := hFinWY
  letI : Finite UWZ := hFinWZ
  have hFinX : Finite VX := Finite.of_injective fY fY.injective
  letI : Finite VX := hFinX
  let Root : Structure L VX := FiniteNamedTraceShadow Family X
  let sY : Structure.Embedding Root
      (FiniteNamedTraceShadow Family Y) :=
    functionalShadowBigEmbedding L Family.ComponentTag
      (fun tag => tag.width Family) fY
  let sZ : Structure.Embedding Root
      (FiniteNamedTraceShadow Family Z) :=
    functionalShadowBigEmbedding L Family.ComponentTag
      (fun tag => tag.width Family) fZ
  let pY : Structure.Embedding Root WY := iY.comp sY
  let pZ : Structure.Embedding Root WZ := iZ.comp sZ
  have hAgree : FiniteNamedComponentLiftsAgreeOn
      Family pY pZ := by
    intro tag xs
    have hEY := fY.map_rel_iff (.inr tag) xs
    have hEZ := fZ.map_rel_iff (.inr tag) xs
    change Y.rel (.inr tag) (sY ∘ xs) ↔
      X.rel (.inr tag) xs at hEY
    change Z.rel (.inr tag) (sZ ∘ xs) ↔
      X.rel (.inr tag) xs at hEZ
    change
      (finiteNamedClosedComponentFoldedLift Family WY).rel
        (.inr tag) (iY ∘ sY ∘ xs) ↔
      (finiteNamedClosedComponentFoldedLift Family WZ).rel
        (.inr tag) (iZ ∘ sZ ∘ xs)
    calc
      _ ↔ Y.rel (.inr tag) (sY ∘ xs) :=
        (hRelY tag (sY ∘ xs)).symm
      _ ↔ X.rel (.inr tag) xs := hEY
      _ ↔ Z.rel (.inr tag) (sZ ∘ xs) := hEZ.symm
      _ ↔ _ := hRelZ tag (sZ ∘ xs)
  let VD := Structure.FreeAmalgam.Vertex Root WY WZ pY pZ
  let D : Structure L VD :=
    Structure.FreeAmalgam.amalgam Root WY WZ pY pZ
  let jWY : Structure.Embedding WY D :=
    Structure.FreeAmalgam.leftEmbedding Root WY WZ pY pZ
  let jWZ : Structure.Embedding WZ D :=
    Structure.FreeAmalgam.rightEmbedding Root WY WZ pY pZ
  have hFree : Structure.IsFreeAmalgam
      pY pZ jWY jWZ :=
    Structure.FreeAmalgam.isFreeAmalgam Root WY WZ pY pZ
  have hAvoidD : AvoidsFiniteNamedEHN Family D :=
    finiteNamedAllComponentLift_freeAmalgam_avoids_of_agreement
      Family D WY WZ jWY jWZ Root pY pZ
      hFree hAgree hAvoidWZ
  have hFinD : Finite VD := by
    let incl : UWY ⊕ UWZ → VD :=
      fun v => match v with
      | .inl y => jWY y
      | .inr z => jWZ z
    apply Finite.of_surjective incl
    intro x
    rcases hFree.covers x with ⟨y, hy⟩ | ⟨z, hz⟩
    · exact ⟨Sum.inl y, hy.symm⟩
    · exact ⟨Sum.inr z, hz.symm⟩
  letI : Finite VD := hFinD
  letI : Fintype VD := Fintype.ofFinite VD
  let dId : Structure.Embedding D D := Structure.Embedding.id D
  obtain ⟨UM, M, hFinM, hAvoidM, eDM, hMaxD⟩ :=
    finiteNamed_exists_finite_maximal_extension
      Family dId hAvoidD
  letI : Finite UM := hFinM
  let rootD : Structure.Embedding D M := eDM.comp dId
  have hMember :
      IsFiniteNamedMaximalTrace Family
        (finiteNamedCanonicalTrace Family rootD) :=
    finiteNamedCanonicalTrace_mem_age Family rootD hAvoidM hMaxD
  let baseY : Structure.Embedding
      (FiniteNamedTraceShadow Family Y) D :=
    jWY.comp iY
  let baseZ : Structure.Embedding
      (FiniteNamedTraceShadow Family Z) D :=
    jWZ.comp iZ
  let jY : Structure.Embedding Y
      (finiteNamedCanonicalTrace Family rootD) :=
    finiteNamedMaximalTrace_embedding_into_allowed_trace
      Family Y WY iY hMaxY hRelY D baseY M
      ⟨hFinM, hAvoidM⟩ rootD (eDM.comp jWY)
      (by intro y; rfl)
  let jZ : Structure.Embedding Z
      (finiteNamedCanonicalTrace Family rootD) :=
    finiteNamedMaximalTrace_embedding_into_allowed_trace
      Family Z WZ iZ hMaxZ hRelZ D baseZ M
      ⟨hFinM, hAvoidM⟩ rootD (eDM.comp jWZ)
      (by intro z; rfl)
  refine ⟨VD, finiteNamedCanonicalTrace Family rootD,
    hMember, jY, jZ, ?_⟩
  intro y z
  change jWY (iY y) = jWZ (iZ z) ↔
      ∃ x : VX, y = fY x ∧ z = fZ x
  constructor
  · intro h
    obtain ⟨x, hy, hz⟩ :=
      (hFree.overlap (iY y) (iZ z)).mp h
    exact ⟨x, iY.injective hy, iZ.injective hz⟩
  · rintro ⟨x, rfl, rfl⟩
    exact (hFree.overlap (iY (fY x)) (iZ (fZ x))).mpr
      ⟨x, rfl, rfl⟩

end AllThoseRamseyClasses.Lifts
