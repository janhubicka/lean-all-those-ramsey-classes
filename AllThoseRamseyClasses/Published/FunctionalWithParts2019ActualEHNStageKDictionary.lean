import AllThoseRamseyClasses.Published.FunctionalWithParts2019OriginalKMembership
import PartiteConstruction.Functional.EHNStage
import PartiteConstruction.Functional.NativeWholePartClosure
import PartiteConstruction.Functional.NativePartialClosure
import PartiteConstruction.Functional.WholeMaskClosednessDictionary2019

/-!
# Appendix Track B: genuine native EHN stages in the canonical 2019 H/K dictionary

The native finite EHN Stage has the ACTUAL source carrier, genuine
transversal set-valued operations, and only the original weak global
part projection. We expose its existing operations as faithful
nonempty-defined Option(Set) functions, preserve its actual vertex
parts as unary predicates, and construct the canonical 2019 tagged
whole-mask relational source on the SAME carrier.

No arbitrary Stage belongs to a chosen original H class. Precisely
when the faithful native partial structure is in H, its canonical
tagged presentation is in K_H. If H is closed-hereditary, an induced
ambient tagged test on S is a K_H member precisely when S is
NATIVE function-closed. Nonclosed weak tests instead remain induced
ambient SEMI-closed test structures and are NOT K_H members.

All theorems preserve the literal tested carrier and its native
function values; no generated closure hull is taken. The result is a
source/class-membership dictionary, not a construction of the local
ambient-relative K-completion axiom or a strict B-tree target.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v

variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {K : Structure.StructureClass (L := L)}
variable {D : Structure L Parts}

/-- The complete 2019 part-labelled OLD tagged representation of the
ACTUAL finite native EHN Stage, using its original vertices, parts,
nonempty-defined native partial operations, and whole-value masks.
No surrogate relational Picture is constructed. -/
noncomputable def genuineEHNStageCanonical2019Tag
    (T : FunctionalPartite.EHN.Stage K D) :
    RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T.Carrier :=
  wholeMaskTagExpansion
    (withPartsWholeMaskOld T.system.toStructure.toNonemptyPartial
      T.system.part)

/-- Exact source class dictionary. On an unchanged genuine native
finite Stage, membership of the complete canonical tagged picture
in K_H is equivalent to membership of its faithful nonempty-defined
functional presentation in the ORIGINAL class H.

No assertion that a FreeAmalgamationClass K of native structures is
the same as H is made; H membership is kept as an explicit condition. -/
theorem genuineEHNStageCanonical2019Tag_mem_iff
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (T : FunctionalPartite.EHN.Stage K D) :
    canonicalGenuineTagged2019Class H
      (genuineEHNStageCanonical2019Tag T) ↔
      H T.system.toStructure.toNonemptyPartial T.system.part := by
  exact canonicalGenuineTagged2019Class_mem_iff H
    T.system.toStructure.toNonemptyPartial T.system.part
    T.system.toNonemptyPartial_fibreTransversal

/-- The exact native function-closed subsets of a real EHN stage are
precisely the subsets whose INDUCED AMBIENT canonical complete-mask
2019 presentation is intrinsically U-closed.

This holds for genuinely MULTIVALUED outputs, since whole-mask
tags use full complete values and their original domain masks.
An arbitrary nonclosed weak S is not completed or replaced by
an ambient closure hull. -/
theorem genuineEHNStage_closed_iff_canonical2019TagInduce_UClosed
    (T : FunctionalPartite.EHN.Stage K D)
    (hPos : L.PositiveFuncArity)
    (S : Set T.Carrier) :
    T.system.toStructure.IsClosed S ↔
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        ((genuineEHNStageCanonical2019Tag T).induce S) := by
  let A := T.system.toStructure.toNonemptyPartial
  have hTr : FibreTransversal A T.system.part :=
    T.system.toNonemptyPartial_fibreTransversal
  have hTrPlus : FibreTransversal (A.withParts T.system.part)
      T.system.part :=
    (A.withParts_fibreTransversal_iff T.system.part).mpr hTr
  have hPlus : (L.withParts Parts).PositiveFuncArity :=
    hPos.withParts
  have hDictionary :
      (A.withParts T.system.part).IsClosed S ↔
        IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
          ((genuineEHNStageCanonical2019Tag T).induce S) := by
    simpa only [genuineEHNStageCanonical2019Tag, withPartsWholeMaskOld, A]
      using (A.withParts T.system.part).isClosed_iff_wholeMaskTaggedInduce_isUClosed
        T.system.part hPlus hTrPlus S
  calc
    T.system.toStructure.IsClosed S ↔ A.IsClosed S :=
      (T.system.toStructure.toNonemptyPartial_isClosed_iff S).symm
    _ ↔ (A.withParts T.system.part).IsClosed S :=
      (A.withParts_isClosed_iff T.system.part S).symm
    _ ↔ IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
          ((genuineEHNStageCanonical2019Tag T).induce S) :=
      hDictionary

/-- A real finite EHN Stage in H, with H hereditary on genuine full
function-closed substructures, has an EXACT closed-test dictionary:

  (canonical tagged Stage)|S belongs to K_H  iff
  S is genuinely closed in the ORIGINAL native function language.

In particular a nonclosed intrinsic weak test is not promoted to a
canonical closed K-member. It must instead be handled by the
ambient-relative semi-closed local completion axiom. -/
theorem genuineEHNStage_inducedCanonicalK_mem_iff_closed
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hHer : GenuinePartiteClosedHereditary2019 H)
    (T : FunctionalPartite.EHN.Stage K D)
    (hH : H T.system.toStructure.toNonemptyPartial T.system.part)
    (hPos : L.PositiveFuncArity)
    (S : Set T.Carrier) :
    canonicalGenuineTagged2019Class H
        ((genuineEHNStageCanonical2019Tag T).induce S) ↔
      T.system.toStructure.IsClosed S := by
  have hBase : canonicalGenuineTagged2019Class H
      (genuineEHNStageCanonical2019Tag T) :=
    (genuineEHNStageCanonical2019Tag_mem_iff H T).mpr hH
  constructor
  · intro hTestK
    have hU : IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        ((genuineEHNStageCanonical2019Tag T).induce S) :=
      canonicalGenuineTagged2019Class_closed H _ hTestK
    exact (genuineEHNStage_closed_iff_canonical2019TagInduce_UClosed
      T hPos S).mpr hU
  · intro hClosed
    have hU : IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        ((genuineEHNStageCanonical2019Tag T).induce S) :=
      (genuineEHNStage_closed_iff_canonical2019TagInduce_UClosed
        T hPos S).mp hClosed
    exact (canonicalGenuineTagged2019Class_inducedClosedHereditary
      H hHer hPos)
        (genuineEHNStageCanonical2019Tag T) hBase S hU

end AllThoseRamseyClasses.Published
