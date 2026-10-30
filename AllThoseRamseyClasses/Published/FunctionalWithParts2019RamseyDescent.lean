import AllThoseRamseyClasses.Published.FunctionalWithParts2019CanonicalKClass
import AllThoseRamseyClasses.Published.Coordinated2019ProfileSparseWitness
import PartiteConstruction.Functional.WholeMaskTagArrow2019
import PartiteConstruction.Functional.WholeMaskPartiteRamseyArrow2019

/-!
# Full Ramsey descent from the corrected tagged 2019 class to genuine functions

The canonical tagged relational K-class is constructed from the
original genuine part-labelled Option(Set) functional class H, not
postulated to consist of canonical K members.

If that actual tagged class is relational Ramsey, its Ramsey witness
is automatically a faithful same-carrier genuine partial-function
H member; the checked full-embedding equivalence and tag-arrow
forgetful theorem recover the genuine PART-PRESERVING functional arrow.

Composing with the verified corrected 2019 coordinated
multiamalgamation Ramsey theorem gives a precise conditional main
endpoint in the original functional language: it requires exactly
the tagged class's remaining corrected 2019 hypotheses, rather than
a new strict functional B-tree induction.

The final implication is not a proof that the original functional
local-completion hypothesis implies the relational tagged one.
Strong partite amalgamation, class isomorphism invariance, correct
irreducible Ramsey ambient class and local completions remain explicit.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Genuine PARTITE Ramsey property for a finite class H of
partial Option(Set) functions, with full embeddings that preserve
the vertex part of every point including isolated ones. -/
def GenuinePartite2019FiniteRamsey
    (H : GenuinePartite2019Class (L := L) (Parts := Parts)) : Prop :=
  ∀ {X Y : Type w} [Finite X] [Finite Y]
    (A : PartialSetStructure L X) (partA : X → Parts)
    (B : PartialSetStructure L Y) (partB : Y → Parts),
    H A partA → H B partB →
    FibreTransversal A partA → FibreTransversal B partB →
    ∀ (κ : Type) [Fintype κ] [Nonempty κ],
    ∃ (Z : Type w) (_ : Finite Z)
      (C : PartialSetStructure L Z) (partC : Z → Parts),
      H C partC ∧ FibreTransversal C partC ∧
      PartPreservingArrow A partA B partB C partC κ

/-- Relational Ramsey of the actual canonical tagged K-image
implies genuine part-preserving Ramsey for the ORIGINAL class H.
No K-class interpretation or original functional target membership
oracle is necessary; both are part of the constructed K definition. -/
theorem genuinePartite2019_ramsey_of_canonicalTagged_ramsey
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hK : FiniteRamseyClass (canonicalGenuineTagged2019Class H)) :
    GenuinePartite2019FiniteRamsey H := by
  classical
  intro X Y hX hY A partA B partB hHA hHB hTA hTB κ hκ hκNonempty
  have hK_A : canonicalGenuineTagged2019Class H
      (wholeMaskTagExpansion (withPartsWholeMaskOld A partA)) :=
    canonicalGenuineTagged2019Class_mem H A partA hHA hTA
  have hK_B : canonicalGenuineTagged2019Class H
      (wholeMaskTagExpansion (withPartsWholeMaskOld B partB)) :=
    canonicalGenuineTagged2019Class_mem H B partB hHB hTB
  obtain ⟨Z, hZ, E, hKE, hArrow⟩ :=
    hK (wholeMaskTagExpansion (withPartsWholeMaskOld A partA))
      (wholeMaskTagExpansion (withPartsWholeMaskOld B partB))
      hK_A hK_B κ
  letI : Finite Z := hZ
  obtain ⟨_, C, partC, hHC, hTC, hEq⟩ := hKE
  have hArrowCan : StructuralRamsey.Arrow
      (wholeMaskTagExpansion (withPartsWholeMaskOld A partA))
      (wholeMaskTagExpansion (withPartsWholeMaskOld B partB))
      (wholeMaskTagExpansion (withPartsWholeMaskOld C partC)) κ := by
    rw [← hEq]
    exact hArrow
  have hOld : StructuralRamsey.Arrow
      (withPartsWholeMaskOld A partA)
      (withPartsWholeMaskOld B partB)
      (withPartsWholeMaskOld C partC) κ :=
    wholeMaskTag_forget_arrow
      (withPartsWholeMaskOld A partA)
      (withPartsWholeMaskOld B partB)
      (wholeMaskTagExpansion (withPartsWholeMaskOld C partC))
      κ hArrowCan
  have hFunctional : PartPreservingArrow
      A partA B partB C partC κ :=
    (partPreservingArrow_iff_withPartsWholeMaskOld
      A partA B partB C partC hTA hTB hTC κ).mpr hOld
  exact ⟨Z, hZ, C, partC, hHC, hTC, hFunctional⟩

/-- The 2019 two-pass theorem already gives a full genuine functional
Ramsey conclusion provided the CANONICAL class of original functional
objects satisfies the corrected relational class axioms.  The
difficult local K-hypothesis is NOT discharged here. -/
theorem genuinePartite2019_ramsey_of_canonicalCoordinated2019
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (R : StructureClass
      (L := (L.withParts Parts).wholeMaskTagLanguage Parts))
    (hR : FiniteRamseyClass R)
    (hRIrred : ∀ {X : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      R E → E.Irreducible)
    (hK : IsCoordinated2019MultiamalgamationClass
      R (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts)) :
    GenuinePartite2019FiniteRamsey H := by
  apply genuinePartite2019_ramsey_of_canonicalTagged_ramsey H
  exact coordinated2019_ramsey_by_profile_sparsening
    R (canonicalGenuineTagged2019Class H)
    ((L.withParts Parts).wholeMaskClosureRules Parts)
    hR hRIrred hK

end AllThoseRamseyClasses.Published
