import AllThoseRamseyClasses.Published.InducedClosed2019RankCollision

/-!
# 2019 Lemma 2.30: remove nonmaximal projected generator supports

This isolates the ONLY generator-size case that can survive the
corrected 2019 rank-j completion theorem: every failure to complete
a source of rank at most j+1 forces the minimum generating support
and its protected projected image to have EXACTLY j+1 distinct
vertices. In particular the projection is injective ON that support.

This is not global injectivity of the protected map and does not
create new generating vertices or a new source closure hull.
The tested source may itself be non-U-closed.

The proof uses the completed projected-rank-drop branch and the
strict finite-image cardinal lemma. It makes no assertion about
the remaining multi-line, injective-maximal source histories.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V : Type v}

/-- Either the original finite test is completable from the old
rank-j invariant, OR every supplied generating support of size
at most j+1 is projected injectively and with maximal size j+1.

The right-hand alternative has no unproved completion premise. -/
theorem inducedClosed2019_completion_or_full_projected_rank
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {Source : RelStructure L U} {D : RelStructure L V}
    {f : U → V}
    [Finite U] [Finite V] [DecidableEq V]
    (hD : IsUClosed rules D)
    (hf : IsInducedClosedUHomomorphismEmbedding rules Source D f)
    (G : Finset U) (hGen : IsUGenerating rules Source (↑G : Set U))
    (j : ℕ) (hCard : G.card ≤ j+1)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (D.induce T) →
      USize rules (D.induce T) ≤ j →
      HasInducedClosedUKCompletion K rules (D.induce T)) :
    HasInducedClosedUKCompletion K rules Source ∨
      ((G.image f).card = j+1 ∧ G.card = j+1 ∧
        Set.InjOn f (↑G : Set U)) := by
  classical
  by_cases hBudget : (G.image f).card ≤ j
  · exact Or.inl
      (inducedClosed2019_completion_of_projected_generators
        hD hf G hGen j hRank hBudget)
  · right
    have hImageLe : (G.image f).card ≤ G.card :=
      Finset.card_image_le
    have hFullImage : (G.image f).card = j+1 := by omega
    have hFullG : G.card = j+1 := by omega
    have hInj : Set.InjOn f (↑G : Set U) := by
      intro x hx y hy hfxfy
      by_contra hxy
      have hStrict : (G.image f).card < G.card :=
        projected_generator_card_lt G f hx hy hxy hfxfy
      omega
    exact ⟨hFullImage, hFullG, hInj⟩

/-- Choosing a MINIMUM intrinsic generating support reduces every
source of U-size <= j+1 to either a genuine corrected K-completion
or a maximal-rank generator image of exactly j+1 distinct vertices.

This keeps weak sources and the original 2019 U-size parameter. -/
theorem inducedClosed2019_completion_or_minimal_generator_saturation
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {Source : RelStructure L U} {D : RelStructure L V}
    {f : U → V}
    [Fintype U] [Finite V] [DecidableEq V]
    (hD : IsUClosed rules D)
    (hf : IsInducedClosedUHomomorphismEmbedding rules Source D f)
    (j : ℕ)
    (hSourceRank : USize rules Source ≤ j+1)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (D.induce T) →
      USize rules (D.induce T) ≤ j →
      HasInducedClosedUKCompletion K rules (D.induce T)) :
    HasInducedClosedUKCompletion K rules Source ∨
      (∃ G : Finset U,
        IsUGenerating rules Source (↑G : Set U) ∧
        G.card = USize rules Source ∧
        G.card = j+1 ∧ (G.image f).card = j+1 ∧
        Set.InjOn f (↑G : Set U)) := by
  classical
  obtain ⟨G, hCard, hGen⟩ := USize_spec rules Source
  have hGSize : G.card ≤ j+1 := hCard.le.trans hSourceRank
  rcases inducedClosed2019_completion_or_full_projected_rank
      hD hf G hGen j hGSize hRank with hCompletion | ⟨hImage,hMax,hInj⟩
  · exact Or.inl hCompletion
  · exact Or.inr ⟨G, hGen, hCard, hMax, hImage, hInj⟩

end AllThoseRamseyClasses.Published
