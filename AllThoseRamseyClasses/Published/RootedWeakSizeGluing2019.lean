import AllThoseRamseyClasses.Published.InducedClosed2019MaximalWeakTwoSide
import PartiteConstruction.Ramsey.ClosureRelativeMapGlue
import PartiteConstruction.Ramsey.ClosureMaximalWeakRankHereditary

/-!
# 2019 corrected weak-size induction: ROOTED exact weak images avoid |A| <= j

The genuine previous weak-j completion invariant W_j does NOT imply
K-completion of a j-vertex source together with an entire prescribed
U-closed A-boundary. The earlier small-WEAK-image A-gluing theorem
therefore has a cardinal obstruction when |A| > j.

Define a useful stronger but still vertex-size-oriented invariant
W_j^A(D): for every weak old subset T of <=j vertices and every
induced embedding a:A->D, the exact induced union T U range(a) has a
corrected K-completion. The large A copy is PRESCRIBED and is not
charged against the j free vertices. No assertion that W_j implies
W_j^A is made here.

For an exact maximal-U-rank weak source freely split into two proper
side pieces of <=j vertices, suppose there are ordinary old-picture
side maps pL,pR whose root images factor through two induced embeddings
of the SAME selected closed A in K. Build the finite weak target
vertex sets from pL[Left] and pR[Right], each of size <=j. Enlarge
them by the two whole A-copies in Old, respectively, and use W_j^A
to complete these exact augmented weak targets.

These two completions have induced embeddings of A before completion,
so protectedness on its closed irreducible test forces the A embeddings
to survive. The existing relative strong K-amalgamation glues the
two completed sides over A. This gives a TRUE corrected completion
of the original exact weak source without any old closed-rank-j
hypothesis or illegal weak-generator extension. Unlike the earlier
small-weak-image result, this works even when |A| > j.

The major open tasks are now stated cleanly: construct W_j^A at EVERY
Picture stage, prove it survives the iteration, and obtain the genuine
common A-root data for the native multi-line history. This file
does not solve either task or prove the general repaired Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Rooted exact weak-size completion invariant: j bounds only the
extra weak OLD vertex set; one whole specified induced A-copy in Old
is available for free in the test carrier.

This predicate is stronger than the ordinary weak-j invariant.
It is NOT claimed to follow from the original local-finiteness axiom,
and the existence of a recursive native Picture realizing it is OPEN. -/
def Has2019RootedWeakSizeCompletions
    {VD VA : Type v}
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (D : RelStructure L VD)
    (A : RelStructure L VA)
    (j : ℕ) : Prop :=
  ∀ (T : Finset VD) (a : Embedding A D),
    T.card ≤ j →
    HasInducedClosedUKCompletion K rules
      (D.induce ((↑T : Set VD) ∪ Set.range a))

/-- If a maximal-U-rank exact weak source has two ordinary bounded
old-Picture maps with a common fixed closed A-boundary, W_j^A(D)
completes the WHOLE free source.

The weak target sides are the exact unions of <=j old image
vertices with the prescribed A-copy, possibly much larger than j
and not assumed intrinsically U-closed. The source is never hulled. -/
theorem inducedClosed2019_maximal_weak_two_maps_glue_of_rooted_Wj
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {H E F C VD VA : Type v}
    {Root : RelStructure L H}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {D : RelStructure L VD}
    {A : RelStructure L VA}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    [Fintype C] [Fintype E] [Fintype F]
    [Finite VD] [Finite VA]
    (hStrong : HasFiniteStrongAmalgamation K)
    (hKIrr : ∀ {Z : Type v} (T : RelStructure L Z),
      K T → T.Irreducible)
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hMax : USize rules Whole = Fintype.card C)
    (hAK : K A) (hAClosed : IsUClosed rules A)
    (pL : E → VD) (pR : F → VD)
    (hpL : Left.IsHomomorphismEmbedding D pL)
    (hpR : Right.IsHomomorphismEmbedding D pR)
    (q : H → VA)
    (aL aR : Embedding A D)
    (hRootL : ∀ x : H, pL (sL x) = aL (q x))
    (hRootR : ∀ x : H, pR (sR x) = aR (q x))
    (j : ℕ)
    (hSizeL : Fintype.card E ≤ j)
    (hSizeR : Fintype.card F ≤ j)
    (hRooted : Has2019RootedWeakSizeCompletions K rules D A j) :
    HasInducedClosedUKCompletion K rules Whole := by
  classical
  letI : Fintype VD := Fintype.ofFinite VD
  letI : Finite VA := inferInstance
  let TLSeed : Finset VD := Finset.univ.image pL
  let TRSeed : Finset VD := Finset.univ.image pR
  let TL : Set VD := (↑TLSeed : Set VD) ∪ Set.range aL
  let TR : Set VD := (↑TRSeed : Set VD) ∪ Set.range aR
  have hSL : TLSeed.card ≤ j := by
    calc
      TLSeed.card ≤ (Finset.univ : Finset E).card :=
        Finset.card_image_le
      _ = Fintype.card E := Finset.card_univ
      _ ≤ j := hSizeL
  have hSR : TRSeed.card ≤ j := by
    calc
      TRSeed.card ≤ (Finset.univ : Finset F).card :=
        Finset.card_image_le
      _ = Fintype.card F := Finset.card_univ
      _ ≤ j := hSizeR
  have hImageL (x : E) : pL x ∈ TL :=
    Or.inl (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)
  have hImageR (x : F) : pR x ∈ TR :=
    Or.inl (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)
  have hAL (x : VA) : aL x ∈ TL := Or.inr ⟨x, rfl⟩
  have hAR (x : VA) : aR x ∈ TR := Or.inr ⟨x, rfl⟩
  let rL : Embedding A (D.induce TL) := {
    toFun := fun x => ⟨aL x, hAL x⟩
    injective := by
      intro x y hxy
      exact aL.injective (congrArg Subtype.val hxy)
    map_rel_iff := fun R z => aL.map_rel_iff R z
  }
  let rR : Embedding A (D.induce TR) := {
    toFun := fun x => ⟨aR x, hAR x⟩
    injective := by
      intro x y hxy
      exact aR.injective (congrArg Subtype.val hxy)
    map_rel_iff := fun R z => aR.map_rel_iff R z
  }
  have hRelativeL : IsUSubstructure rules Whole (Set.range iL) :=
    all_subsets_relative_of_USize_eq_card rules Whole hMax
      (Set.range iL)
  have hRelativeR : IsUSubstructure rules Whole (Set.range iR) :=
    all_subsets_relative_of_USize_eq_card rules Whole hMax
      (Set.range iR)
  have hMaxL : USize rules Left = Fintype.card E :=
    Embedding.USize_eq_card_of_embedding_into_maximal hMax iL
  have hMaxR : USize rules Right = Fintype.card F :=
    Embedding.USize_eq_card_of_embedding_into_maximal hMax iR
  have hProtectedL : IsClosedUHomomorphismEmbedding rules Left D pL :=
    hpL.toClosedMap_of_max_USize hMaxL
  have hProtectedR : IsClosedUHomomorphismEmbedding rules Right D pR :=
    hpR.toClosedMap_of_max_USize hMaxR
  let gL : E → TL := fun x => ⟨pL x, hImageL x⟩
  let gR : F → TR := fun x => ⟨pR x, hImageR x⟩
  have hgL : IsClosedUHomomorphismEmbedding rules
      Left (D.induce TL) gL :=
    hProtectedL.codRestrict TL hImageL
  have hgR : IsClosedUHomomorphismEmbedding rules
      Right (D.induce TR) gR :=
    hProtectedR.codRestrict TR hImageR
  have hCompatL (x : H) : gL (sL x) = rL (q x) := by
    apply Subtype.ext
    exact hRootL x
  have hCompatR (x : H) : gR (sR x) = rR (q x) := by
    apply Subtype.ext
    exact hRootR x
  have hDL : HasClosedUKCompletion K rules (D.induce TL) :=
    (inducedClosedKCompletion_iff_abstract_2019).mp
      (hRooted TLSeed aL hSL)
  have hDR : HasClosedUKCompletion K rules (D.induce TR) :=
    (inducedClosedKCompletion_iff_abstract_2019).mp
      (hRooted TRSeed aR hSR)
  have hWhole : HasClosedUKCompletion K rules Whole :=
    HasClosedUKCompletion.of_independent_projected_completions_relative
      rules hStrong hKIrr hFree hRelativeL hRelativeR
      A hAK hAClosed
      (D.induce TL) (D.induce TR)
      gL gR hgL hgR q rL rR hCompatL hCompatR hDL hDR
  exact (inducedClosedKCompletion_iff_abstract_2019).mpr hWhole

end AllThoseRamseyClasses.Published
