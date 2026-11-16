import AllThoseRamseyClasses.Published.TrackEGenuineWithParts2019InternalBCover
import AllThoseRamseyClasses.Published.TrackENativeIrreducibleInternalBCover2019

/-!
# Track E: assemble native internal B-coverage on the SAME actual final witness

This is a candidate integration proof. The tagged internal-copy certificate
and the true partial-function Ramsey arrow come from the same selected C.
The native copy extension is obtained without changing C or its vertices.
Do not mark validated until full exact-head Lean and axiom checks pass.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Actual coordinated fully-partial Ramsey target retaining INTERNAL
canonical tagged B-extensions, same selected HE and every literal
small-weak K-completion on one same final C. -/
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
      IrreduciblesExtendTo (genuineWithPartsTagged2019 B partB) C ∧
      (∀ S : Finset VQ, S.card ≤ n →
        HasInducedClosedUKCompletion K
          ((L.withParts Parts).wholeMaskClosureRules Parts)
          (C.induce (↑S : Set VQ))) ∧
      FibreTransversal (wholeMaskOriginalDecode C)
        (wholeMaskCoveredPart C B partB hC hCover) ∧
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
  obtain ⟨VQ, hFinite, C, hC, hCover, hRest⟩ :=
    genuineWithParts2019_final_functional_arrow_with_internalB
      A partA B partB C0 hTransA hTransB hPos
      hBK hClosed hHer hStrong hKIrr n κ hArrow0
  letI : Finite VQ := hFinite
  rcases hRest with ⟨hProjection, hInternal, hWeak, hTrans, hArrow⟩
  have hBK' : K (wholeMaskTagExpansion
      ((B.withParts partB).wholeMaskPatternGraph partB)) := by
    simpa only [genuineWithPartsTagged2019] using hBK
  have hCover' : ∀ {T : Type w}
      (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((B.withParts partB).wholeMaskPatternGraph partB))) := by
    simpa only [genuineWithPartsTagged2019] using hCover
  have hInternal' : IrreduciblesExtendTo
      (wholeMaskTagExpansion
        ((B.withParts partB).wholeMaskPatternGraph partB)) C := by
    simpa only [genuineWithPartsTagged2019] using hInternal
  have hNative :
      ∀ {T : Type w} (E : Structure L T),
        E.Irreducible →
        ∀ e : Structure.Embedding E
          ((wholeMaskOriginalDecode C).collapseDomain),
          ∃ beta : Structure.Embedding B.collapseDomain
            ((wholeMaskOriginalDecode C).collapseDomain),
            ∀ x : T, ∃ b : Y, e x = beta b := by
    intro T E hE e
    exact wholeMaskCovered_nativeIrredCopy_internalB
      C B partB hTransB hC hPos hBK' hHer hKIrr
      hCover' hInternal' E hE e
  exact ⟨VQ, hFinite, C, hC, hCover,
    hProjection, hInternal, hWeak, hTrans, hArrow, hNative⟩

end AllThoseRamseyClasses.Published
