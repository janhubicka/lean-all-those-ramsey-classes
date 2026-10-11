import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosureProjectedGenerators

/-!
# 2019 Lemma 2.30: the genuine projected-rank-drop/collision branch

The missing general j -> j+1 Picture theorem involves several
different cases. This file proves the RANK-DROP branch entirely in
the paper-faithful corrected Definition 2.15 convention:

Let a finite possibly WEAK induced source F have a protected map
f:F->D into a finite U-closed control D. Suppose all closed induced
substructures of D of U-size <=j have corrected K-completions.

If an actual finite generating support G of F projects to at most
j distinct vertices, then F admits a corrected (K,U)-completion.
In particular, if |G|<=j+1 and two DISTINCT generators collide
under f, the projected cardinal bound is automatic.

The source F is NEVER replaced by cl_D(f[F]). Its projected
generator set is used only to select a closed rank-j target hull;
the corrected completed map is pulled back to the ORIGINAL F.
A is not assumed U-closed. No forbidden completion of an
arbitrary weak generating subset is extended to its prescribed hull.

This is a verified branch only. The remaining maximal-rank
injective-generator/multi-line history still requires a true
completion/compatible-boundary construction and is NOT proved here.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V : Type v}

/-- Any finite ORIGINAL source whose projected generating set
has at most j vertices has an exact corrected K-completion.
The closed target rank-j invariant is stated using original
induced tests, and the target hull is merely an intermediate. -/
theorem inducedClosed2019_completion_of_projected_generators
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {Source : RelStructure L U} {D : RelStructure L V}
    {f : U → V}
    [Finite U] [Finite V]
    (hD : IsUClosed rules D)
    (hf : IsInducedClosedUHomomorphismEmbedding rules Source D f)
    (G : Finset U) (hGen : IsUGenerating rules Source (↑G : Set U))
    (j : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (D.induce T) →
      USize rules (D.induce T) ≤ j →
      HasInducedClosedUKCompletion K rules (D.induce T))
    (hBudget : (G.image f).card ≤ j) :
    HasInducedClosedUKCompletion K rules Source := by
  classical
  have hRankAbstract :
      ∀ (T : Set V) [Fintype T],
        IsUClosed rules (D.induce T) →
        USize rules (D.induce T) ≤ j →
        HasClosedUKCompletion K rules (D.induce T) := by
    intro T hFT hT hSize
    letI : Fintype T := hFT
    exact (inducedClosedKCompletion_iff_abstract_2019).mp
      (hRank T hT hSize)
  have hAbstract :
      HasClosedUKCompletion K rules Source :=
    HasClosedUKCompletion.of_projected_generators
      hD (IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hf)
      G hGen j hRankAbstract hBudget
  exact (inducedClosedKCompletion_iff_abstract_2019).mpr hAbstract

/-- Concrete collision subcase of the j->j+1 induction: whenever
a source generator set of size at most j+1 contains two distinct
vertices with equal protected projection, the source already
has a genuine corrected completion.

The remainder of the higher-rank Picture theorem is not asserted. -/
theorem inducedClosed2019_completion_of_generator_collision
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {Source : RelStructure L U} {D : RelStructure L V}
    {f : U → V}
    [Finite U] [Finite V]
    (hD : IsUClosed rules D)
    (hf : IsInducedClosedUHomomorphismEmbedding rules Source D f)
    (G : Finset U) (hGen : IsUGenerating rules Source (↑G : Set U))
    (j : ℕ) (hCard : G.card ≤ j+1)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (D.induce T) →
      USize rules (D.induce T) ≤ j →
      HasInducedClosedUKCompletion K rules (D.induce T))
    {x y : U} (hx : x ∈ G) (hy : y ∈ G)
    (hxy : x ≠ y) (hImage : f x = f y) :
    HasInducedClosedUKCompletion K rules Source := by
  classical
  have hProjectedCard : (G.image f).card ≤ j := by
    have hStrict : (G.image f).card < G.card :=
      projected_generator_card_lt G f hx hy hxy hImage
    omega
  exact inducedClosed2019_completion_of_projected_generators
    hD hf G hGen j hRank hProjectedCard

end AllThoseRamseyClasses.Published
