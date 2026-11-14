import AllThoseRamseyClasses.Published.Coordinated2019ProfileSparseWitness

/-!
# Track E: recover ALL exact small K-completions from a protected tagged HE

The original coordinated 2019 sparse proof obtains exact weak-test
K-completions from the strict first-stage local Bplus graph-tree
certificates, an ordinary HE from the current noncanonical tagged
witness Q to the CANONICAL tagged profile control Ptag, and external
closed-U/U-irreducible protected Btag test coverage.

The argument DOES NOT use the particular construction history of Q.
Consequently any NEW finite U-closed, Btag-protected tagged source
Q' with the SAME selected ordinary HE to Ptag has the same exact
small-test K-relative completions, even if Q' was enlarged by an
extra Btag attachment pass.

This is exactly the boundary needed after a future U-closed
internal-B saturation: rather than transport all old small-test
completions through each attachment, RECONSTRUCT them on the literal
S subset of the FINAL augmented source by projecting S to P.
The size bound uses card(image q S) <= card(S), with NO hull and
no change of tested vertex carrier.

This theorem alone does not produce Q', internal B-coverage or a
genuine partial functional decoder. They belong to separate steps.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Exact original-language K-completion of EVERY small induced test
of any protected tagged candidate Q, using the actual selected
ordinary HE to a previously strict-profile-sparsened P.

The old selected Q need NOT be the particular old Hales-Jewett Q
obtained from the second pass. This makes the result reusable on an
externally B-protected U-closed POSTPROCESSED final tagged source. -/
theorem profile2019_exactWeak_K_completions_of_protected_taggedHE
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {UB VP VQ : Type v} [Finite VP] [Finite VQ]
    (Base : RelStructure L UB)
    (hBase : IsUClosed rules Base)
    (hBK : K Base)
    (hClosed : ∀ {X : Type v} (E : RelStructure L X),
      K E → IsUClosed rules E)
    (hHer : ClosedUHereditary K rules)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hKIrr : ∀ {X : Type v} (E : RelStructure L X),
      K E → E.Irreducible)
    (P : RelStructure (closureProfileLanguage2019 rules Base) VP)
    (n : ℕ)
    (hLocalP : ∀ T : Finset VP, T.card ≤ n →
      HasTreeCompletion
        (closureProfileExpansion2019 rules Base Base)
        (P.induce (↑T : Set VP)))
    (Q : RelStructure (profileRootTagLanguage2019 rules Base) VQ)
    (hQClosed : IsUClosed (profileRootTagRules2019 rules Base) Q)
    (hQCover : ∀ {Z : Type v}
      (Test : RelStructure (profileRootTagLanguage2019 rules Base) Z),
      IsUClosed (profileRootTagRules2019 rules Base) Test →
      IsUIrreducible (profileRootTagRules2019 rules Base) Test →
      Embedding Test Q →
      Nonempty (Embedding Test
        (profileTaggedCanonical2019 rules Base Base)))
    (q : VQ → VP)
    (hQControl : Q.IsHomomorphismEmbedding
      (profileRootTagExpansion2019 rules Base P) q) :
    ∀ S : Finset VQ, S.card ≤ n →
      HasInducedClosedUKCompletion K rules
        ((profileRootTagOriginal2019 Base Q).induce
          (↑S : Set VQ)) := by
  classical
  let Qplus := profileRootTagReduct2019 Base Q
  let Qold := profileRootTagOriginal2019 Base Q
  obtain ⟨_hQOldClosed, hQOldCover⟩ :=
    profileTag2019_original_closed_and_coverage
      Base hBase Q hQClosed hQCover
  have hQOrdPlus : Qplus.IsHomomorphismEmbedding P q :=
    profileRootTagReduct2019_ordinary
      Base Q (profileRootTagExpansion2019 rules Base P) q hQControl
  intro S hS
  let T : Finset VP := S.image q
  have hTCard : T.card ≤ n := (Finset.card_image_le).trans hS
  have hSMap : (Qplus.induce (↑S : Set VQ)).IsHomomorphismEmbedding P
      (fun x : (↑S : Set VQ) => q x.1) :=
    hQOrdPlus.comp
      (inclusion Qplus (↑S : Set VQ)).isHomomorphismEmbedding
  have hImage : ∀ x : (↑S : Set VQ),
      q x.1 ∈ (↑T : Set VP) := by
    intro x
    exact Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩
  let toImage : (↑S : Set VQ) → (↑T : Set VP) :=
    fun x => ⟨q x.1, hImage x⟩
  have hToImage : (Qplus.induce (↑S : Set VQ)).IsHomomorphismEmbedding
      (P.induce (↑T : Set VP)) toImage :=
    hSMap.codRestrict (↑T : Set VP) hImage
  obtain ⟨WT, Tree, hTree, fTree, hfTree⟩ := hLocalP T hTCard
  have hSTree : HasTreeCompletion
      (closureProfileExpansion2019 rules Base Base)
      (Qplus.induce (↑S : Set VQ)) :=
    ⟨WT, Tree, hTree, fTree ∘ toImage, hfTree.comp hToImage⟩
  obtain ⟨XE, hXE, E, hKE, fE, hfE⟩ :=
    closureProfile2019_tree_completion_to_K
      Base hBase hBK hClosed hHer hStrong
      (Qplus.induce (↑S : Set VQ)) hSTree
  have hOrdOld : (Qold.induce (↑S : Set VQ)).IsHomomorphismEmbedding
      E fE :=
    profileReduct2019_ordinary Base
      (Qplus.induce (↑S : Set VQ))
      (closureProfileExpansion2019 rules Base E) fE hfE
  have hSCover : ∀ {Z : Type v} (Test : RelStructure L Z),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test (Qold.induce (↑S : Set VQ)) →
      Nonempty (Embedding Test Base) := by
    intro Z Test hTestClosed hTestIrred e
    exact hQOldCover Test hTestClosed hTestIrred
      ((inclusion Qold (↑S : Set VQ)).comp e)
  have hEMap : IsInducedClosedUHomomorphismEmbedding rules
      (Qold.induce (↑S : Set VQ)) E fE :=
    ordinary2019_corrected_of_closed_coverage
      Base (Qold.induce (↑S : Set VQ)) E
      hBK hHer hKIrr hSCover fE hOrdOld
  exact ⟨XE, hXE, E, hKE, hKIrr E hKE, fE, hEMap⟩

end AllThoseRamseyClasses.Published
