import AllThoseRamseyClasses.Published.FunctionalWithParts2019ActualHSparseWitness
import AllThoseRamseyClasses.Published.FunctionalWithParts2019GlobalProtectedControl

/-!
# Track E: retain the ACTUAL corrected tagged global HE witness

The existing exact-H 2019 sparse-witness theorem exports a SOURCE-DEFINED
genuine-partial control homomorphism. Its underlying two-pass construction
actually produced a stronger corrected 2019 INDuced-closed U-homomorphism-
embedding `hTag` to the CANONICAL tagged control on the very same f.

This new theorem keeps that certified hTag IN ADDITION to the already
checked source-defined original control law, the actual recovered part
map, full protected B coverage, all exact n-vertex H-valued weak
completion certificates, and the full part-preserving Ramsey arrow.

It reuses the SAME 2019 two-pass construction once. We do NOT claim
that hTag protects arbitrary native irreducible tests: obtaining a FULL
canonical tagged lift of each such test into the final noncanonical
relational C remains an independent Track E2 obligation.

No manifold or weak source is replaced by a closure hull, no extra
control projection is chosen, and no domain reflection is asserted.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- An exact H-valued genuine partial-function 2019 Ramsey witness
which RETAINS the actual corrected tagged global
`IsInducedClosedUHomomorphismEmbedding` for its ORIGINAL control map.

The same f also has the source-defined original whole-value law and
preserves the recovered vertex parts. All H-relative completion tests
are the literal induced C|S for every |S| ≤ n; no generated hull.
-/
theorem genuinePartite2019_actual_sparse_witness_with_taggedHE_control
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
    (hArrow0 : PartPreservingArrow A partA B partB C0 part0 κ) :
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
        IsInducedClosedUHomomorphismEmbedding
          ((L.withParts Parts).wholeMaskClosureRules Parts)
          C (genuineWithPartsTagged2019 C0 part0) f ∧
        IsOriginalPartialHomomorphism (wholeMaskOriginalDecode C) C0 f ∧
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
      hWeak, hTr, hArrow⟩ :=
    genuineWithParts2019_actual_functional_ramsey_witness
      A partA B partB C0 part0
      hTransA hTransB hTrans0 hPos
      (K := K) hBK hClosedK hHerK hStrongK hKIrr
      n κ hArrow0
  letI : Finite VQ := hVQ
  obtain ⟨f, hTag⟩ := hControl
  have hOriginal :
      IsOriginalPartialHomomorphism (wholeMaskOriginalDecode C) C0 f ∧
      (∀ x : VQ,
        part0 (f x) = wholeMaskCoveredPart C B partB hC hCover x) :=
    wholeMaskOriginalDecode_originalPartialControl_of_tagHom
      C B partB hC hPos hCover C0 part0 f hTag.1
  have hHCompletions :
      ∀ S : Finset VQ, S.card ≤ n →
        HasGenuinePartiteTagged2019RelativeCompletion H
          (C.induce (↑S : Set VQ)) := by
    intro S hSize
    exact (canonicalGenuineTagged2019_KCompletion_iff_relative
      H (C.induce (↑S : Set VQ))).mp (hWeak S hSize)
  exact ⟨VQ, hVQ, C, hC, hCover,
    ⟨f, hTag, hOriginal.1, hOriginal.2⟩,
    hHCompletions, hTr, hArrow⟩

end AllThoseRamseyClasses.Published
