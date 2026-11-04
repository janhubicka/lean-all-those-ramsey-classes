import AllThoseRamseyClasses.Published.FunctionalWithParts2019ActualEHNStageKDictionary
import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeKCompletion
import PartiteConstruction.Functional.WholeMaskWholeWeakUSize2019

/-!
# Appendix Track B: exact weak ranks and local completion on genuine EHN stages

The previous verified class bridge characterizes precisely which
AMBIENT-induced 2019 tagged weak tests of an actual native EHN stage
belong to the canonical genuine H class: exactly the function-CLOSED
ones, provided the genuine native stage is in H and H is hereditary.

This module checks the separate quantitative dictionary needed for
the corrected 2019 local-completion cutoff: on the SAME literal weak
vertex set S, the whole-fibre Option(Set) weak functional closure
of the ACTUAL native EHN stage is exactly 2019 U-closure inside
the ambient-induced complete-mask tagged structure on S. The
minimum number of weak generators is therefore its USize.

The part-label expansion leaves functions and their closure alone.
It is essential nevertheless: 2019 H/K-membership is defined with
named unary predicates for the part of *every* vertex, even isolated
ones. No rank is computed on a generated ambient hull and no
new source Picture is constructed.

Finally we specialize the independently verified exact genuine
relative local-completion equivalence to this actual Stage/weak set.
It is an equivalence of COMPLETION PROPOSITIONS, never an assertion
that the completion axiom holds.

Warning: these statements use the whole-fibre weak Option(Set)
restriction. For a multivalued function partially meeting S,
clipped weak restriction is different, and its rank may differ.
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

/-- The actual native EHN Stage's genuinely partial whole-fibre
weak closure of Q INSIDE the literal tested S equals 2019 U-closure
of Q in the induced AMBIENT complete-mask tagged stage on the
SAME vertices. The expanded part-label predicates do not alter
any generated vertex and no ambient closure hull is taken. -/
theorem genuineEHNStage_wholeWeakFunctionClosure_eq_taggedUClosure
    (T : FunctionalPartite.EHN.Stage K D)
    (hPos : L.PositiveFuncArity)
    (S : Set T.Carrier) (Q : Set S) :
    (wholeWeakInduce T.system.toStructure.toNonemptyPartial S).functionClosure Q =
      UClosureHull ((L.withParts Parts).wholeMaskClosureRules Parts)
        ((genuineEHNStageCanonical2019Tag T).induce S) Q := by
  let A := T.system.toStructure.toNonemptyPartial
  have hTr : FibreTransversal A T.system.part :=
    T.system.toNonemptyPartial_fibreTransversal
  have hTrPlus : FibreTransversal (A.withParts T.system.part)
      T.system.part :=
    (A.withParts_fibreTransversal_iff T.system.part).mpr hTr
  have hPlus : (L.withParts Parts).PositiveFuncArity :=
    hPos.withParts
  calc
    (wholeWeakInduce A S).functionClosure Q =
        (wholeWeakInduce (A.withParts T.system.part) S).functionClosure Q :=
      (A.withParts_wholeWeak_functionClosure_eq T.system.part S Q).symm
    _ = UClosureHull ((L.withParts Parts).wholeMaskClosureRules Parts)
        ((genuineEHNStageCanonical2019Tag T).induce S) Q := by
      simpa only [genuineEHNStageCanonical2019Tag,
        withPartsWholeMaskOld, A] using
        (A.withParts T.system.part).wholeWeakFunctionClosure_eq_inducedAmbientUClosureHull
          T.system.part hPlus hTrPlus S Q

/-- Exact minimum number of weak generators of a real native EHN
Stage, computed under genuine whole-fibre Option(Set) weak restriction,
is precisely the 2019 USize of the ambient tagged weak test on the
literal same carrier S. No K_H membership or closure of S is assumed.
Both predicates refer to the SAME cutoff n. -/
theorem genuineEHNStage_wholeWeakGeneratedByAtMost_iff_taggedUSize
    (T : FunctionalPartite.EHN.Stage K D)
    (hPos : L.PositiveFuncArity)
    (S : Set T.Carrier) [Fintype S] (n : ℕ) :
    (wholeWeakInduce T.system.toStructure.toNonemptyPartial S).GeneratedByAtMost n ↔
      USize ((L.withParts Parts).wholeMaskClosureRules Parts)
        ((genuineEHNStageCanonical2019Tag T).induce S) ≤ n := by
  let A := T.system.toStructure.toNonemptyPartial
  have hTr : FibreTransversal A T.system.part :=
    T.system.toNonemptyPartial_fibreTransversal
  have hTrPlus : FibreTransversal (A.withParts T.system.part)
      T.system.part :=
    (A.withParts_fibreTransversal_iff T.system.part).mpr hTr
  have hPlus : (L.withParts Parts).PositiveFuncArity :=
    hPos.withParts
  calc
    (wholeWeakInduce A S).GeneratedByAtMost n ↔
        (wholeWeakInduce (A.withParts T.system.part) S).GeneratedByAtMost n :=
      (A.withParts_wholeWeak_generatedByAtMost_iff T.system.part S n).symm
    _ ↔ USize ((L.withParts Parts).wholeMaskClosureRules Parts)
        ((genuineEHNStageCanonical2019Tag T).induce S) ≤ n := by
      simpa only [genuineEHNStageCanonical2019Tag,
        withPartsWholeMaskOld, A] using
        (A.withParts T.system.part).wholeWeakGeneratedByAtMost_iff_inducedAmbientUSize_le
          T.system.part hPlus hTrPlus S n

/-- Exact local-completion distinction on an actual EHN native
stage: a corrected induced-closed K_H,U completion of its AMBIENT
tagged weak test is exactly a genuine H-valued relative completion
in the same induced ambient relational language.

The tagged source and the literal weak carrier S are unchanged.
This does NOT assert that either completion exists and does not
turn an intrinsic original partial homomorphism into an ambient
tagged U-homomorphism-embedding. The latter is Track C's missing
local-completion hypothesis, not an automatic source dictionary. -/
theorem genuineEHNStage_exactWeak_KCompletion_iff_HRelative
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (T : FunctionalPartite.EHN.Stage K D)
    (S : Set T.Carrier) :
    HasInducedClosedUKCompletion
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      ((genuineEHNStageCanonical2019Tag T).induce S) ↔
    HasGenuinePartiteTagged2019RelativeCompletion H
      ((genuineEHNStageCanonical2019Tag T).induce S) :=
  canonicalGenuineTagged2019_KCompletion_iff_relative H _

end AllThoseRamseyClasses.Published
