import AllThoseRamseyClasses.Published.ProfileStrictTreeCompletion2019
import AllThoseRamseyClasses.Published.ProfileRootTagTransfer2019
import AllThoseRamseyClasses.Published.InducedClosed2019UnrestrictedInitial
import PartiteConstruction.Iterated.SparseningStrictBaseIrreducible

/-!
# Actual unrestricted sparse witness for the coordinated 2019 theorem

This construction does NOT assume the native closed-rank increment.
It first makes the original Ramsey control closed, canonically records
all generated closed Base boundaries, and applies the checked purely
relational strict-tree sparsening theorem. A second unrestricted closed
Picture pass in the fresh root-tagged language then makes the original
reduct closed while retaining the exact weak-test completions.

The ORIGINAL control C0 and the ORIGINAL cutoff n are unchanged.
Every tested weak source keeps its exact original vertices; only its
finite IMAGE in the relational sparse witness is used, with cardinal
at most the original source cardinal. No completion of generators is
extended to a prescribed closed hull. No compatible-boundary or
sparse-witness constructor is taken as a premise.

This is an alternative proof of the corrected main theorem; it does
not establish the separate native Lemma 2.30 rank-increment assertion.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Construct the exact sparse witness above the SAME original Ramsey
control, for EVERY preselected weak-vertex cutoff n. All geometric,
closure, and boundary data are built by the proved profile/tag route. -/
theorem coordinated2019_profile_sparse_witness
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {UA VB P0 : Type v} [Finite UA] [Finite VB] [Finite P0]
    (A : RelStructure L UA) (B : RelStructure L VB) (C0 : RelStructure L P0)
    (hA : IsUClosed rules A) (hB : IsUClosed rules B) (hBK : K B)
    (hClosed : ∀ {X : Type v} (E : RelStructure L X), K E → IsUClosed rules E)
    (hHer : ClosedUHereditary K rules) (hStrong : HasFiniteStrongAmalgamation K)
    (hKIrr : ∀ {X : Type v} (E : RelStructure L X), K E → E.Irreducible)
    (n : ℕ) (κ : Type) [Fintype κ] [Nonempty κ]
    (hArrow0 : StructuralRamsey.Arrow A B C0 κ) :
    HasInducedClosed2019SparseWitness K rules A B C0 n κ := by
  classical
  obtain ⟨VD, hVD, D, hArrowD, hDClosed, hDPart, _hDCover⟩ :=
    StructuralRamsey.Partite.Induced.closed_ramsey_unrestricted
      A B C0 hA hB κ hArrow0
  letI : Finite VD := hVD
  let Aplus := closureProfileExpansion2019 rules B A
  let Bplus := closureProfileExpansion2019 rules B B
  let Dplus := closureProfileExpansion2019 rules B D.toRelStructure
  have hArrowPlus : StructuralRamsey.Arrow Aplus Bplus Dplus κ :=
    closureProfile2019_arrow B A B D.toRelStructure hA hB hDClosed κ hArrowD
  have hBplusIrr : Bplus.Irreducible :=
    (closureProfile2019_base_hereditarily_irreducible B hB).irreducible
  obtain ⟨VP, hVP, P, hArrowP, p, hp, hLocalP, _hPExt⟩ :=
    StructuralRamsey.Partite.IteratedSparsening.sparseningRamsey_strict_baseIrreducible_all
      Aplus Bplus Dplus κ hArrowPlus hBplusIrr n
  letI : Finite VP := hVP
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
  let Qplus := profileRootTagReduct2019 B Q.toRelStructure
  let Qold := profileRootTagOriginal2019 B Q.toRelStructure
  obtain ⟨hQOldClosed, hQOldCover⟩ :=
    profileTag2019_original_closed_and_coverage B hB Q.toRelStructure hQClosed hQCover
  have hQOrdTag : Q.toRelStructure.IsHomomorphismEmbedding Ptag Q.part :=
    hQPart.toHomomorphismEmbedding_of_closed hQClosed
  have hQOrdPlus : Qplus.IsHomomorphismEmbedding P Q.part :=
    profileRootTagReduct2019_ordinary B Q.toRelStructure Ptag Q.part hQOrdTag
  have hQDPlus : Qplus.IsHomomorphismEmbedding Dplus (p ∘ Q.part) := hp.comp hQOrdPlus
  have hQDOrd : Qold.IsHomomorphismEmbedding D.toRelStructure (p ∘ Q.part) :=
    profileReduct2019_ordinary B Qplus Dplus (p ∘ Q.part) hQDPlus
  have hQD : IsInducedClosedUHomomorphismEmbedding rules
      Qold D.toRelStructure (p ∘ Q.part) :=
    ordinary2019_corrected_of_closed_coverage B Qold D.toRelStructure
      hBK hHer hKIrr hQOldCover (p ∘ Q.part) hQDOrd
  have hQC0 : IsInducedClosedUHomomorphismEmbedding rules
      Qold C0 (D.part ∘ (p ∘ Q.part)) :=
    inducedClosedMap_comp_2019
      (IsClosedUHomomorphismEmbedding.toInducedClosed hDPart) hQD
  have hKCover : CorrectedUIrreduciblesIn K rules Qold :=
    ClosedUIrreduciblesIn.toCorrectedInduced
      (ClosedUIrreduciblesIn.of_copy_coverage hHer B hBK Qold hQOldCover)
  have hOriginalArrow : StructuralRamsey.Arrow A B Qold κ :=
    profileRootTag2019_forget_arrow B A B Q.toRelStructure hA hB κ hArrowQ
  have hWeak : ∀ S : Finset VQ, S.card ≤ n →
      HasInducedClosedUKCompletion K rules (Qold.induce (↑S : Set VQ)) := by
    intro S hS
    let T : Finset VP := S.image Q.part
    have hTCard : T.card ≤ n := (Finset.card_image_le).trans hS
    have hSMap : (Qplus.induce (↑S : Set VQ)).IsHomomorphismEmbedding P
        (fun x : (↑S : Set VQ) => Q.part x.1) :=
      hQOrdPlus.comp (inclusion Qplus (↑S : Set VQ)).isHomomorphismEmbedding
    have hImage : ∀ x : (↑S : Set VQ), Q.part x.1 ∈ (↑T : Set VP) := by
      intro x
      exact Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩
    let toImage : (↑S : Set VQ) → (↑T : Set VP) := fun x => ⟨Q.part x.1, hImage x⟩
    have hToImage : (Qplus.induce (↑S : Set VQ)).IsHomomorphismEmbedding
        (P.induce (↑T : Set VP)) toImage := hSMap.codRestrict (↑T : Set VP) hImage
    obtain ⟨WT, Tree, hTree, fTree, hfTree⟩ := hLocalP T hTCard
    have hSTree : HasTreeCompletion Bplus (Qplus.induce (↑S : Set VQ)) :=
      ⟨WT, Tree, hTree, fTree ∘ toImage, hfTree.comp hToImage⟩
    obtain ⟨XE, hXE, E, hKE, fE, hfE⟩ :=
      closureProfile2019_tree_completion_to_K B hB hBK hClosed hHer hStrong
        (Qplus.induce (↑S : Set VQ)) hSTree
    have hOrdOld : (Qold.induce (↑S : Set VQ)).IsHomomorphismEmbedding E fE :=
      profileReduct2019_ordinary B (Qplus.induce (↑S : Set VQ))
        (closureProfileExpansion2019 rules B E) fE hfE
    have hSCover : ∀ {Z : Type v} (Test : RelStructure L Z),
        IsUClosed rules Test → IsUIrreducible rules Test →
        Embedding Test (Qold.induce (↑S : Set VQ)) → Nonempty (Embedding Test B) := by
      intro Z Test hTestClosed hTestIrred e
      exact hQOldCover Test hTestClosed hTestIrred
        ((inclusion Qold (↑S : Set VQ)).comp e)
    have hEMap : IsInducedClosedUHomomorphismEmbedding rules
        (Qold.induce (↑S : Set VQ)) E fE :=
      ordinary2019_corrected_of_closed_coverage B (Qold.induce (↑S : Set VQ)) E
        hBK hHer hKIrr hSCover fE hOrdOld
    exact ⟨XE, hXE, E, hKE, hKIrr E hKE, fE, hEMap⟩
  exact ⟨VQ, hVQ, Qold, hQOldClosed, ⟨D.part ∘ (p ∘ Q.part), hQC0⟩,
    hKCover, hWeak, hOriginalArrow⟩

/-- The unrestricted coordinated corrected 2019 Ramsey theorem.

Only the corrected class assumptions, including explicit invariance
under isomorphism, are premises. The sparse witness is constructed;
there is NO native-rank, boundary, or sparse-constructor hypothesis.
The published literal theorem and native Lemma 2.30 are distinct. -/
theorem coordinated2019_ramsey_by_profile_sparsening
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (hR : FiniteRamseyClass R)
    (hRIrred : ∀ {X : Type v} (C : RelStructure L X), R C → C.Irreducible)
    (hK : IsCoordinated2019MultiamalgamationClass R K rules) :
    FiniteRamseyClass K := by
  have hHer : ClosedUHereditary K rules :=
    embeddedClosedHereditary_of_induced hK.induced.hereditary hK.iso
  have hKIrr : ∀ {X : Type v} (C : RelStructure L X), K C → C.Irreducible := by
    intro X C hKC
    exact hRIrred C (hK.induced.subset C hKC)
  apply inducedClosed2019_ramsey_of_sparse_witnesses R K rules hR hRIrred hK.induced
  intro X Y Z hX hY hZ A B C0 n κ hκ hκNonempty hKA hKB _hRC0 hArrow
  exact coordinated2019_profile_sparse_witness A B C0
    (hK.induced.closed A hKA) (hK.induced.closed B hKB) hKB
    hK.induced.closed hHer hK.induced.strong hKIrr n κ hArrow

end AllThoseRamseyClasses.Published
