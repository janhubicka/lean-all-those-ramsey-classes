import AllThoseRamseyClasses.Published.TrackEPostprocessTaggedSparseInternalB2019

/-!
# Track E: SAME actual coordinated 2019 witness, now with INTERNAL B-extension

This is the actual, unconditional (under the ORIGINAL corrected 2019
relational class conditions) coordinated two-pass sparse witness
CONSTRUCTION, not an abstract postprocessing oracle.

English proof:
1. Build the original U-closed initial Ramsey picture over the unchanged
   control C0 using the already verified unrestricted closed Ramsey pass.
2. Expand by generated closure B-profiles and use the existing strict
   RELATIONAL iterated sparsening theorem on Aplus/Bplus/Dplus. KEEP
   its genuine internal Bplus-coverage hPExt as well as hLocalP.
3. Fresh-tag Aplus/Bplus/P. Build the actual second unrestricted closed
   Ramsey picture Q, with hQCover and the selected HE q=Q.part into Ptag.
4. Apply the exact finite postprocessing theorem to THIS Q and THIS P.
   The first strict profile P already has Bplus internal coverage.
   Canonical tagging transfers it to the SAME Ptag. The postprocessing
   adds compatible Btag copies along U-CLOSED hulls to create Qnew,
   retaining the original selected q on all old Q vertices, protected
   closed U-test coverage, U-closedness, and the Ramsey arrow.
5. RECONSTRUCT exact small K-completions at every literal S⊆Qnew with
   |S|≤n directly from the original hLocalP and the Qnew→Ptag HE.
6. Forget tagged/profile layers. Original closedness and external
   protected Base-test coverage descend. INTERNAL Btag extensions
   descend to INTERNAL original Base copies in the SAME final Qold.
   Compose ordinary HE through P and the initial D to the ORIGINAL C0
   and upgrade to induced-closed U-HE using B-coverage + K hereditariness.

Nothing enlarges any TEST S to its closure; U-hulls are used only as
final B-ATTACHMENT roots. No extra generator, class, target or cutoff
assumption is introduced.

This theorem is for corrected RELATIONAL 2019 U-closed sparsening with
the exact K-local completion contract. It is not a literal proof of
the historically false total-function-fibre global projection, nor
the optional strict full FUNCTION-language B-tree local theorem.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- The ACTUAL corrected 2019 relational coordinated construction
produces one finite U-closed witness with full Ramsey arrow, SAME
original control and exact K-completion cutoff, protected external B
tests, and INTERNAL Base-extension of every ordinary irreducible
source substructure, all simultaneously.

No new hypothesis beyond the checked original two-pass profile
construction is needed; the added finite B-padding is constructed
using its first strict profile stage's retained internal Bplus
extension certificate. -/
theorem coordinated2019_profile_sparse_witness_with_INTERNAL_B_coverage
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {UA VB P0 : Type v} [Finite UA] [Finite VB] [Finite P0]
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C0 : RelStructure L P0)
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (hBK : K B)
    (hClosed : ∀ {X : Type v} (E : RelStructure L X),
      K E → IsUClosed rules E)
    (hHer : ClosedUHereditary K rules)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hKIrr : ∀ {X : Type v} (E : RelStructure L X),
      K E → E.Irreducible)
    (n : ℕ) (κ : Type) [Fintype κ] [Nonempty κ]
    (hArrow0 : StructuralRamsey.Arrow A B C0 κ) :
    ∃ (Z : Type v) (_ : Finite Z) (C : RelStructure L Z),
      IsUClosed rules C ∧
      (∃ f : Z → P0,
        IsInducedClosedUHomomorphismEmbedding rules C C0 f) ∧
      (∀ {T : Type v} (Test : RelStructure L T),
        IsUClosed rules Test → IsUIrreducible rules Test →
        Embedding Test C → Nonempty (Embedding Test B)) ∧
      IrreduciblesExtendTo B C ∧
      (∀ S : Finset Z, S.card ≤ n →
        HasInducedClosedUKCompletion K rules
          (C.induce (↑S : Set Z))) ∧
      StructuralRamsey.Arrow A B C κ := by
  classical
  obtain ⟨VD, hVD, D, hArrowD, hDClosed, hDPart, _hDCover⟩ :=
    StructuralRamsey.Partite.Induced.closed_ramsey_unrestricted
      A B C0 hA hB κ hArrow0
  letI : Finite VD := hVD
  let Aplus := closureProfileExpansion2019 rules B A
  let Bplus := closureProfileExpansion2019 rules B B
  let Dplus := closureProfileExpansion2019 rules B D.toRelStructure
  have hArrowPlus : StructuralRamsey.Arrow Aplus Bplus Dplus κ :=
    closureProfile2019_arrow B A B D.toRelStructure hA hB hDClosed
      κ hArrowD
  have hBplusIrr : Bplus.Irreducible :=
    (closureProfile2019_base_hereditarily_irreducible B hB).irreducible
  obtain ⟨VP, hVP, P, hArrowP, p, hp, hLocalP, hPExt⟩ :=
    StructuralRamsey.Partite.IteratedSparsening.sparseningRamsey_strict_baseIrreducible_all
      Aplus Bplus Dplus κ hArrowPlus hBplusIrr n
  letI : Finite VP := hVP
  have hLocalTree : ∀ T : Finset VP, T.card ≤ n →
      HasTreeCompletion Bplus (P.induce (↑T : Set VP)) := by
    intro T hT
    obtain ⟨WT, Tree, hTree, fTree, hfTree⟩ := hLocalP T hT
    exact ⟨WT, Tree, hTree, fTree, hfTree⟩
  let Atag := profileRootTagExpansion2019 rules B Aplus
  let Btag := profileRootTagExpansion2019 rules B Bplus
  let Ptag := profileRootTagExpansion2019 rules B P
  have hArrowTag : StructuralRamsey.Arrow Atag Btag Ptag κ :=
    profileRootTag2019_arrow B Aplus Bplus P κ hArrowP
  have hAtagClosed : IsUClosed (profileRootTagRules2019 rules B) Atag :=
    profileRootTag2019_closed_canonical B Aplus hA
  have hBtagClosed : IsUClosed (profileRootTagRules2019 rules B) Btag :=
    profileRootTag2019_closed_canonical B Bplus hB
  obtain ⟨VQ, hVQ, Q, hArrowQ, hQClosed, hQPart, hQCover⟩ :=
    StructuralRamsey.Partite.Induced.closed_ramsey_unrestricted
      Atag Btag Ptag hAtagClosed hBtagClosed κ hArrowTag
  letI : Finite VQ := hVQ
  have hQOrdTag : Q.toRelStructure.IsHomomorphismEmbedding Ptag Q.part :=
    hQPart.toHomomorphismEmbedding_of_closed hQClosed
  obtain ⟨W, hW, Qnew, _j, qNew, hQnewClosed, hQnewHE,
      _hQnewOldMap, hQnewCover, _hQnewInternal,
      hQnewOriginalInternal, hQnewWeak, hQnewArrow⟩ :=
    profile2019_postprocess_tagged_sparse_with_internalB
      B hB hBK hClosed hHer hStrong hKIrr
      P n hLocalTree hPExt
      Atag Q.toRelStructure hQClosed hQCover
      Q.part hQOrdTag κ hArrowQ
  letI : Finite W := hW
  let Qplus := profileRootTagReduct2019 B Qnew
  let Qold := profileRootTagOriginal2019 B Qnew
  obtain ⟨hQoldClosed, hQoldCover⟩ :=
    profileTag2019_original_closed_and_coverage
      B hB Qnew hQnewClosed hQnewCover
  have hQOrdPlus : Qplus.IsHomomorphismEmbedding P qNew :=
    profileRootTagReduct2019_ordinary
      B Qnew Ptag qNew hQnewHE
  have hQDPlus : Qplus.IsHomomorphismEmbedding Dplus (p ∘ qNew) :=
    hp.comp hQOrdPlus
  have hQDOrd : Qold.IsHomomorphismEmbedding D.toRelStructure
      (p ∘ qNew) :=
    profileReduct2019_ordinary
      B Qplus Dplus (p ∘ qNew) hQDPlus
  have hQD : IsInducedClosedUHomomorphismEmbedding
      rules Qold D.toRelStructure (p ∘ qNew) :=
    ordinary2019_corrected_of_closed_coverage
      B Qold D.toRelStructure hBK hHer hKIrr
      hQoldCover (p ∘ qNew) hQDOrd
  have hQC0 : IsInducedClosedUHomomorphismEmbedding
      rules Qold C0 (D.part ∘ (p ∘ qNew)) :=
    inducedClosedMap_comp_2019
      (IsClosedUHomomorphismEmbedding.toInducedClosed hDPart) hQD
  have hOriginalArrow : StructuralRamsey.Arrow A B Qold κ :=
    profileRootTag2019_forget_arrow
      B A B Qnew hA hB κ hQnewArrow
  exact ⟨W, hW, Qold, hQoldClosed,
    ⟨D.part ∘ (p ∘ qNew), hQC0⟩,
    hQoldCover, hQnewOriginalInternal, hQnewWeak,
    hOriginalArrow⟩

end AllThoseRamseyClasses.Published
