import AllThoseRamseyClasses.Published.FunctionalWithParts2019ActualRamseyWitness
import AllThoseRamseyClasses.Published.FunctionalWithParts2019OriginalKMembership
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CanonicalKStrongAmalgamation
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CanonicalKIso
import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeKCompletion
import PartiteConstruction.Functional.WholeMaskCoveredFunctionalControlProjection2019

/-!
# Actual genuine functional 2019 sparse Ramsey witness, WITH original H-completions

The already verified two-pass 2019 profile sparsening constructs a
relational tagged closed Picture C with final canonical B-copy coverage,
an actual genuine Option(Set) part-preserving Ramsey arrow, and
induced-closed K-local completion of EVERY small exact weak induced S.

Here K is not an arbitrary relational completion class: it is defined
as the full tagged whole-mask presentation of genuine partial
part-transversal members of an original functional class H.

From actual H-partite strong amalgamation, H-closed hereditary
membership, H-isomorphism invariance and canonical H-irreducibility,
derive the 2019 structural hypotheses of the two-pass construction.
The resulting K-completion of each exact C.induce S automatically
has a target that is a GENUINE H-member (with the correct part map,
undefined/defined-empty domain data and original vertex carrier).

The final global tagged control projection also decodes into a TRUE
original-source-defined partial homomorphism of the final functional
Ramsey target back to the given original functional witness C0,
preserving every vertex part. Every closed U-irreducible tagged test
in C is covered by a full canonical B-copy, not postulated separately.

No 2019 local-finiteness CLASS AXIOM is used to construct this sparse
witness: the local weak completions follow from the verified two-pass
partite B-tree/profile construction and strong H-partite amalgamation.
The class-level Ramsey theorem needs the *additional* corrected
local axiom to complete the entire output into H.

The local certificates are AMBIENT-relative completions of C.induce S;
they are not an assertion that every intrinsic weak functional test
has a full functional embedding. This is not the old strict
function-language B-tree completion theorem of the survey.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Starting from an ACTUAL genuine partite functional Ramsey arrow,
construct the corrected 2019 two-pass FINAL functional Ramsey target
together with actual H-valued exact weak K-completion certificates.

The exact n-vertex weak cutoff is fixed in advance, and neither S
nor its projected image is replaced by a generated closure hull.
The final functional target need not itself belong to H until the
separate corrected class-level local-completion axiom is applied. -/
theorem genuinePartite2019_actual_sparse_witness_with_H_completions
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hHer : GenuinePartiteClosedHereditary2019 H)
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (hPos : L.PositiveFuncArity)
    (hIrr : ∀ {T : Type w} [Finite T]
      (D : PartialSetStructure L T) (p : T → Parts),
      H D p → FibreTransversal D p →
      (wholeMaskTagExpansion (withPartsWholeMaskOld D p)).Irreducible)
    {X Y Z : Type w}
    [Finite X] [Finite Y] [Finite Z]
    (A : PartialSetStructure L X) (partA : X → Parts)
    (B : PartialSetStructure L Y) (partB : Y → Parts)
    (C0 : PartialSetStructure L Z) (part0 : Z → Parts)
    (hB : H B partB)
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
    (hTrans0 : FibreTransversal C0 part0)
    (n : ℕ) (κ : Type) [Fintype κ] [Nonempty κ]
    (hArrow0 : PartPreservingArrow
      A partA B partB C0 part0 κ) :
    ∃ (VQ : Type w) (_ : Finite VQ)
      (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) VQ)
      (hC : IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
      (hCover : ∀ {T : Type w}
        (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
        IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
        IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
        Embedding Test C →
        Nonempty (Embedding Test (genuineWithPartsTagged2019 B partB))),
      (∃ f : VQ → Z,
        IsOriginalPartialHomomorphism
          (wholeMaskOriginalDecode C) C0 f ∧
        (∀ x : VQ,
          part0 (f x) = wholeMaskCoveredPart C B partB hC hCover x)) ∧
      (∀ S : Finset VQ, S.card ≤ n →
        HasGenuinePartiteTagged2019RelativeCompletion H
          (C.induce (↑S : Set VQ))) ∧
      FibreTransversal (wholeMaskOriginalDecode C)
        (wholeMaskCoveredPart C B partB hC hCover) ∧
      PartPreservingArrow A partA B partB
        (wholeMaskOriginalDecode C)
        (wholeMaskCoveredPart C B partB hC hCover) κ := by
  classical
  let K : StructureClass (L := (L.withParts Parts).wholeMaskTagLanguage Parts) :=
    canonicalGenuineTagged2019Class H
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  have hBK : K (genuineWithPartsTagged2019 B partB) :=
    canonicalGenuineTagged2019Class_mem H B partB hB hTransB
  have hClosedK : ∀ {T : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
      K E → IsUClosed rules E :=
    canonicalGenuineTagged2019Class_closed H
  have hHerInd : InducedClosed2019Hereditary K rules :=
    canonicalGenuineTagged2019Class_inducedClosedHereditary
      H hHer hPos
  have hIsoK : IsomorphismClosed2019 K :=
    canonicalGenuineTagged2019Class_isomorphismClosed H hIso
  have hHerK : ClosedUHereditary K rules :=
    embeddedClosedHereditary_of_induced hHerInd hIsoK
  have hStrongK : HasFiniteStrongAmalgamation K :=
    canonicalGenuineTagged2019Class_strongAmalgamation H hStrong
  have hKIrr : ∀ {T : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
      K E → E.Irreducible := by
    intro T E hE
    obtain ⟨hFinite, D, partD, hHD, hTrD, hEq⟩ := hE
    letI : Finite T := hFinite
    rw [hEq]
    exact hIrr D partD hHD hTrD
  obtain ⟨VQ, hVQ, C, hC, hCover, hControl,
      hWeak, hTrans, hRamsey⟩ :=
    genuineWithParts2019_actual_functional_ramsey_witness
      A partA B partB C0 part0
      hTransA hTransB hTrans0 hPos
      (K := K) hBK hClosedK hHerK hStrongK hKIrr
      n κ hArrow0
  letI : Finite VQ := hVQ
  obtain ⟨f, hf⟩ := hControl
  have hOriginalControl :
      IsOriginalPartialHomomorphism
        (wholeMaskOriginalDecode C) C0 f ∧
      (∀ x : VQ,
        part0 (f x) = wholeMaskCoveredPart C B partB hC hCover x) :=
    wholeMaskOriginalDecode_originalPartialControl_of_tagHom
      C B partB hC hPos hCover C0 part0 f hf.1
  have hHCompletions :
      ∀ S : Finset VQ, S.card ≤ n →
        HasGenuinePartiteTagged2019RelativeCompletion H
          (C.induce (↑S : Set VQ)) := by
    intro S hSize
    exact (canonicalGenuineTagged2019_KCompletion_iff_relative
      H (C.induce (↑S : Set VQ))).mp (hWeak S hSize)
  refine ⟨VQ, hVQ, C, hC, hCover,
    ⟨f, hOriginalControl⟩, hHCompletions, hTrans, hRamsey⟩

end AllThoseRamseyClasses.Published
