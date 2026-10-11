import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosureProjectedRankGlue

/-!
# 2019 Lemma 2.30: corrected mixed-cut K-completion with honest budgets

The remaining higher-rank Picture construction must handle a closed
test F crossing multiple attached copies, with no common variable
coordinate. The source may split as a free amalgam of U-semi-closed
sides over a U-closed separator, but that split does NOT by itself
lower either projected absolute U-size. The shared boundary can be
expensive. A four-vertex counterexample to this tempting shortcut
is recorded in partite-construction's irreducible-hulls note.

This theorem proves the COMPLETION/GLUING half rigorously in the
paper-faithful corrected Definition 2.15 map convention, given the
actual numerical and embedding certificates that the Picture geometry
must provide:

* a genuine free source split with closed common root;
* one corrected positive projection of the EXACT whole source into
  the original finite U-closed previous picture D;
* the projected separator inside one embedded closed A∈K;
* separate finite source-side generating sets whose projected
  image cardinalities are each <= j;
* all closed U-size<=j induced substructures of D admit corrected
  K-completions.

The same closed K-boundary is constructed by the pinned
ClosureProjectedRankGlue theorem; strong K-amalgamation combines
the independent completions. The final source remains the ORIGINAL
unclosed-or-closed F and its completion map is corrected-induced,
not a completion of a substituted projected hull.

The hard missing task is to extract the two ABSOLUTE projected
j-budgets from actual native multi-line Hales--Jewett histories.
We do not assert that every free cut has those budgets or that the
general rank j->j+1 step is proved.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- The mixed free-cut/completion gluing theorem for the proposed
2019 corrected U-homomorphism-embedding, with every geometric
and numerical premise visible and no unproved boundary oracle. -/
theorem inducedClosed2019_completion_of_projected_mixed_cut
    {K : StructureClass.{u,v} (L := L)}
    (rules : ClosureDescription L)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {X : Type v} (T : RelStructure L X),
      K T → T.Irreducible)
    {UA H E F C V : Type v}
    {A : RelStructure L UA} {D : RelStructure L V}
    {Root : RelStructure L H}
    {Left : RelStructure L E} {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    [Finite V] [DecidableEq V]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hRoot : IsUClosed rules Root)
    (hLeft : IsUSemiClosed rules Left)
    (hRight : IsUSemiClosed rules Right)
    (hKA : K A) (hA : IsUClosed rules A)
    (hD : IsUClosed rules D)
    (a : Embedding A D)
    (p : C → V)
    (hp : IsInducedClosedUHomomorphismEmbedding rules Whole D p)
    (hSeparator : ∀ r : H, p (iL (sL r)) ∈ Set.range a)
    (GLeft : Finset E) (GRight : Finset F)
    (hGL : IsUGenerating rules Left (↑GLeft : Set E))
    (hGR : IsUGenerating rules Right (↑GRight : Set F))
    (j : ℕ)
    (hBudgetL : (GLeft.image (p ∘ iL)).card ≤ j)
    (hBudgetR : (GRight.image (p ∘ iR)).card ≤ j)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (D.induce T) →
      USize rules (D.induce T) ≤ j →
      HasInducedClosedUKCompletion K rules (D.induce T)) :
    HasInducedClosedUKCompletion K rules Whole := by
  have hAbstractRank :
      ∀ (T : Set V) [Fintype T],
        IsUClosed rules (D.induce T) →
        USize rules (D.induce T) ≤ j →
        HasClosedUKCompletion K rules (D.induce T) := by
    intro T hFT hT hSize
    letI : Fintype T := hFT
    exact (inducedClosedKCompletion_iff_abstract_2019).mp
      (hRank T hT hSize)
  have hHerEmbedded :
      ∀ {X Y : Type v}
        {E : RelStructure L X} {F : RelStructure L Y},
        K F → IsUClosed rules E → Embedding E F → K E := by
    intro X Y E F hF hE e
    exact hHer E F hF hE e
  have hAbstract : HasClosedUKCompletion K rules Whole :=
    HasClosedUKCompletion.of_common_projection_generators
      rules hStrong hHerEmbedded hKIrr
      hSrc hRoot hLeft hRight hKA hA hD a p
      (IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hp)
      hSeparator GLeft GRight hGL hGR
      j hBudgetL hBudgetR hAbstractRank
  exact (inducedClosedKCompletion_iff_abstract_2019).mpr hAbstract

end AllThoseRamseyClasses.Published
