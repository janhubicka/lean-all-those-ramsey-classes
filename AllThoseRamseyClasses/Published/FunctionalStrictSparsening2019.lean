import AllThoseRamseyClasses.Published.FunctionalStrictProfileClosedTree2019
import AllThoseRamseyClasses.Published.Coordinated2019ProfileSparseWitness

/-!
# Strict functional sparsening in the 2019 closure-description language

The construction is *functional*: the output is genuinely U-closed, every
small original weak test maps by the corrected U-homomorphism-embedding
into a strict tree of U-closed original Base copies. The strict target
records closed gluing roots at each node. No relational graph-tree
target or loose full-functional tree is silently substituted.

For protected-map transfer we presently assume hereditary ordinary
irreducibility of Base. This holds for ordered expansions. All other
steps reuse the fully built unrestricted closed 2019 Picture, the
ordinary profile sparsening and final tagged closed pass.

Neither a native higher-rank Hales–Jewett increment nor the full
set-valued-fibre encoding is asserted here.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- A source has an exact weak-test completion into a genuinely
U-closed *strict* tree of original Base copies. The map protects all
closed U-irreducible induced substructures but is not required to
reflect undefined function roots globally. -/
def HasClosedStrictTreeCompletion2019
    {VB V : Type v} (rules : ClosureDescription L)
    (Base : RelStructure L VB) (C : RelStructure L V) : Prop :=
  ∃ (W : Type v) (_ : Finite W) (T : RelStructure L W),
    UClosedStrictTreeAmalgam rules Base W T ∧
    ∃ f : V → W, IsInducedClosedUHomomorphismEmbedding rules C T f

/-- A positive ordinary relational homomorphism-embedding is a corrected
2019 U-homomorphism-embedding when every closed U-irreducible source
test already embeds into a hereditarily ordinarily irreducible Base.

This is a *genuine* protected-test transfer, not a change to the
notion of ordinary irreducibility. -/
theorem ordinary_to_closed2019_of_hereditarily_irreducible_base
    {VB V W : Type v} {rules : ClosureDescription L}
    (Base : RelStructure L VB) (hBase : HereditarilyIrreducible Base)
    (C : RelStructure L V) (Target : RelStructure L W)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test C → Nonempty (Embedding Test Base))
    (f : V → W) (hf : C.IsHomomorphismEmbedding Target f) :
    IsInducedClosedUHomomorphismEmbedding rules C Target f := by
  refine ⟨hf.1, ?_⟩
  intro S hSClosed hSIrred
  obtain ⟨eB⟩ :=
    hCover (C.induce S) hSClosed hSIrred (inclusion C S)
  exact hf.embeddingOn S (hBase.of_embedding eB)

/-- Construct a genuinely closed Ramsey witness with a strict
U-closed Base-tree completion for EVERY exact weak test of at most n
original vertices.

The projection is the corrected U-HE to the unchanged C0. No finite
generating rank or closed-hull cardinality is substituted for n.
All auxiliary profile/tree/tag languages are discharged in the output. -/
theorem coordinated2019_strict_functional_sparse_witness
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {UA VB P0 : Type v} [Finite UA] [Finite VB] [Finite P0]
    (A : RelStructure L UA) (B : RelStructure L VB)
    (C0 : RelStructure L P0)
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (hBHer : HereditarilyIrreducible B)
    (hBK : K B) (hHer : ClosedUHereditary K rules)
    (n : ℕ) (κ : Type) [Fintype κ] [Nonempty κ]
    (hArrow0 : StructuralRamsey.Arrow A B C0 κ) :
    ∃ (Z : Type v) (_ : Finite Z) (C : RelStructure L Z),
      IsUClosed rules C ∧
      (∃ f : Z → P0,
        IsInducedClosedUHomomorphismEmbedding rules C C0 f) ∧
      (∀ {X : Type v} (Test : RelStructure L X),
        IsUClosed rules Test → IsUIrreducible rules Test →
        Embedding Test C → Nonempty (Embedding Test B)) ∧
      (∀ S : Finset Z, S.card ≤ n →
        HasClosedStrictTreeCompletion2019 rules B
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
    profileTag2019_original_closed_and_coverage
      B hB Q.toRelStructure hQClosed hQCover
  have hQOrdTag : Q.toRelStructure.IsHomomorphismEmbedding Ptag Q.part :=
    hQPart.toHomomorphismEmbedding_of_closed hQClosed
  have hQOrdPlus : Qplus.IsHomomorphismEmbedding P Q.part :=
    profileRootTagReduct2019_ordinary B Q.toRelStructure Ptag Q.part hQOrdTag
  have hQDPlus : Qplus.IsHomomorphismEmbedding Dplus (p ∘ Q.part) :=
    hp.comp hQOrdPlus
  have hQDOrd : Qold.IsHomomorphismEmbedding D.toRelStructure (p ∘ Q.part) :=
    profileReduct2019_ordinary B Qplus Dplus (p ∘ Q.part) hQDPlus
  have hQD : IsInducedClosedUHomomorphismEmbedding
      rules Qold D.toRelStructure (p ∘ Q.part) :=
    ordinary_to_closed2019_of_hereditarily_irreducible_base
      B hBHer Qold D.toRelStructure hQOldCover (p ∘ Q.part) hQDOrd
  have hQC0 : IsInducedClosedUHomomorphismEmbedding
      rules Qold C0 (D.part ∘ (p ∘ Q.part)) :=
    inducedClosedMap_comp_2019
      (IsClosedUHomomorphismEmbedding.toInducedClosed hDPart) hQD
  have hOriginalArrow : StructuralRamsey.Arrow A B Qold κ :=
    profileRootTag2019_forget_arrow B A B Q.toRelStructure hA hB κ hArrowQ
  have hWeak : ∀ S : Finset VQ, S.card ≤ n →
      HasClosedStrictTreeCompletion2019 rules B
        (Qold.induce (↑S : Set VQ)) := by
    intro S hS
    let T : Finset VP := S.image Q.part
    have hTCard : T.card ≤ n := (Finset.card_image_le).trans hS
    have hSMap : (Qplus.induce (↑S : Set VQ)).IsHomomorphismEmbedding P
        (fun x : (↑S : Set VQ) => Q.part x.1) :=
      hQOrdPlus.comp (inclusion Qplus (↑S : Set VQ)).isHomomorphismEmbedding
    have hImage : ∀ x : (↑S : Set VQ), Q.part x.1 ∈ (↑T : Set VP) := by
      intro x
      exact Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩
    let toImage : (↑S : Set VQ) → (↑T : Set VP) :=
      fun x => ⟨Q.part x.1, hImage x⟩
    have hToImage : (Qplus.induce (↑S : Set VQ)).IsHomomorphismEmbedding
        (P.induce (↑T : Set VP)) toImage :=
      hSMap.codRestrict (↑T : Set VP) hImage
    obtain ⟨WT, Tree, hTree, fTree, hfTree⟩ := hLocalP T hTCard
    obtain ⟨XE, hXE, E, hETree, fE, hCopy⟩ :=
      closureProfile2019_strict_tree_closedRoot_completion
        B hB (hBHer.irreducible) hBK hHer Tree hTree
    have hTreeMap :
        Tree.IsHomomorphismEmbedding
          (closureProfileExpansion2019 rules B E) fE :=
      hCopy.toHomomorphismEmbedding_of_strictTree hTree
    let sourceMap : (↑S : Set VQ) → XE := fE ∘ (fTree ∘ toImage)
    have hPlusMap :
        (Qplus.induce (↑S : Set VQ)).IsHomomorphismEmbedding
          (closureProfileExpansion2019 rules B E) sourceMap :=
      hTreeMap.comp (hfTree.comp hToImage)
    have hOrdOld :
        (Qold.induce (↑S : Set VQ)).IsHomomorphismEmbedding E sourceMap :=
      profileReduct2019_ordinary B (Qplus.induce (↑S : Set VQ))
        (closureProfileExpansion2019 rules B E) sourceMap hPlusMap
    have hSCover : ∀ {X : Type v} (Test : RelStructure L X),
        IsUClosed rules Test → IsUIrreducible rules Test →
        Embedding Test (Qold.induce (↑S : Set VQ)) →
        Nonempty (Embedding Test B) := by
      intro X Test hTestClosed hTestIrred e
      exact hQOldCover Test hTestClosed hTestIrred
        ((inclusion Qold (↑S : Set VQ)).comp e)
    have hEMap :
        IsInducedClosedUHomomorphismEmbedding rules
          (Qold.induce (↑S : Set VQ)) E sourceMap :=
      ordinary_to_closed2019_of_hereditarily_irreducible_base
        B hBHer (Qold.induce (↑S : Set VQ)) E
        hSCover sourceMap hOrdOld
    exact ⟨XE, hXE, E, hETree, sourceMap, hEMap⟩
  exact ⟨VQ, hVQ, Qold, hQOldClosed,
    ⟨D.part ∘ (p ∘ Q.part), hQC0⟩,
    hQOldCover, hWeak, hOriginalArrow⟩

end AllThoseRamseyClasses.Published
