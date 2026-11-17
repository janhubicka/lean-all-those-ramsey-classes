import AllThoseRamseyClasses.Published.TrackEGenuinePartialArrowInternalBCover2019
import AllThoseRamseyClasses.Published.TrackENativeIrreducibleInternalBCover2019

/-!
# Track E — the same final Ramsey witness covers every native irreducible

This module assembles two independently proved results on the *same* actual
2019 two-pass whole-mask witness.  In particular, no fresh target, hull
replacement, or additional Ramsey pass is introduced.

The conclusion is still a partial-function part-preserving Ramsey arrow
together with full native B-copy coverage of every irreducible native
substructure.  It does not assert the final H-membership or the strict
full-function B-tree theorem.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Final same-source bridge: the genuine functional Ramsey target and
all its full native irreducible copies are covered by genuine native
B-copies, not merely by external tagged tests. -/
theorem genuineWithParts2019_final_arrow_and_native_internalB
    {X Y Z : Type w}
    [Finite X] [Finite Y] [Finite Z]
    (A : PartialSetStructure L X) (partA : X → Parts)
    (B : PartialSetStructure L Y) (partB : Y → Parts)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
    (hPos : L.PositiveFuncArity)
    {K : StructureClass (L := (L.withParts Parts).wholeMaskTagLanguage Parts)}
    (hBK : K (genuineWithPartsTagged2019 B partB))
    (hClosed : ∀ {T : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
      K E → IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) E)
    (hHer : ClosedUHereditary K
      ((L.withParts Parts).wholeMaskClosureRules Parts))
    (hStrong : HasFiniteStrongAmalgamation K)
    (hKIrr : ∀ {T : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
      K E → E.Irreducible)
    (n : ℕ) (κ : Type) [Fintype κ] [Nonempty κ]
    (hArrow0 : StructuralRamsey.Arrow
      (genuineWithPartsTagged2019 A partA)
      (genuineWithPartsTagged2019 B partB) C0 κ) :
    ∃ (VQ : Type w) (_ : Finite VQ)
      (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) VQ)
      (hC : IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
      (hCover : ∀ {T : Type w}
        (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
        IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
        IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
        Embedding Test C →
        Nonempty (Embedding Test (genuineWithPartsTagged2019 B partB))),
      (∃ f : VQ → Z, IsInducedClosedUHomomorphismEmbedding
        ((L.withParts Parts).wholeMaskClosureRules Parts) C C0 f) ∧
      (∀ S : Finset VQ, S.card ≤ n →
        HasInducedClosedUKCompletion K
          ((L.withParts Parts).wholeMaskClosureRules Parts)
          (C.induce (↑S : Set VQ))) ∧
      PartPreservingArrow A partA B partB
        (wholeMaskOriginalDecode C)
        (wholeMaskCoveredPart C B partB hC hCover) κ ∧
      (∀ {T : Type w} (E : Structure L T),
        E.Irreducible →
        ∀ e : Structure.Embedding E
          ((wholeMaskOriginalDecode C).collapseDomain),
          ∃ beta : Structure.Embedding B.collapseDomain
            ((wholeMaskOriginalDecode C).collapseDomain),
            ∀ x : T, ∃ b : Y, e x = beta b) := by
  classical
  obtain ⟨VQ, hFinite, C, hC, hCover,
    hSelected, hInternal, hWeak, hTrans, hArrow⟩ :=
    genuineWithParts2019_final_functional_arrow_with_internalB
      A partA B partB C0 hTransA hTransB hPos
      hBK hClosed hHer hStrong hKIrr n κ hArrow0
  letI : Finite VQ := hFinite
  refine ⟨VQ, hFinite, C, hC, hCover,
    hSelected, hWeak, hArrow, ?_⟩
  intro T E hE e
  exact wholeMaskCovered_nativeIrredCopy_internalB
    C B partB hTransB hC hPos hBK hHer hKIrr
    hCover hInternal E hE e

end AllThoseRamseyClasses.Published
