import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosureMaximalWeakOrdinaryABoundary

/-!
# 2019 Lemma 2.30: exact weak maximal-rank gluing via TWO ordinary side maps

The already verified native Hales--Jewett history gives different
coordinate/identity retractions for different sides of a transverse
family. A single global protected map into the old picture is NOT
available in general. The earlier corrected mixed-cut theorem with
one global map is therefore insufficient.

At maximum intrinsic U-size, the exact weak source is closure
independent: all its induced sides have maximum U-rank, and an
ORDINARY homomorphism-embedding of each side automatically protects
all closed U-irreducible embedded tests (no closure hull is substituted).

The pinned partite-construction library proves that two DIFFERENT
ordinary side maps into the old U-closed picture D can be completed
and glued by strong K-amalgamation, provided the root images factor
through two embeddings of the SAME fixed U-closed A in K. Its proof
constructs the genuine shared closed K-boundary by taking the
U-closure of q[Root] INSIDE A. No intrinsic closedness of the
original weak source, its sides, or its common root is assumed.

Here we transport that theorem to the paper-faithful corrected
Definition 2.15/2.17 induced-test completion convention, preserving
the original exact source carrier.

The second theorem derives both side rank-j vertex-cardinality
budgets from a genuinely PROPER source free cut at total size ≤j+1.
Thus projected rank budgets need not be separately postulated
in that case.

What remains genuinely OPEN is the actual-history factorization:
the one-line-deletion native coordinate retractions must yield
ordinary side maps and ROOT-COMPATIBLE factorizations through two
embedded selected A-copies. Equality of part labels alone does
NOT imply these embeddings exist.

No universal rank-j to j+1 Picture constructor, and no unrestricted
corrected Theorem 2.18, is claimed here.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Repaired 2019 weak-source maximal-U-rank completion from
two possibly DIFFERENT ordinary side maps with common A-root
factorization. No pre-existing closed K-boundary and no
U-closedness of the root/sides/source are assumed.

The previous rank-j premise still quantifies over exact U-closed
induced tests in D; it does not quantify over closures in place
of the tested weak source. -/
theorem inducedClosed2019_maximal_weak_two_ordinary_side_maps_via_A
    {K : StructureClass.{u,v} (L := L)}
    (rules : ClosureDescription L)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {Z : Type v} (T : RelStructure L Z),
      K T → T.Irreducible)
    {H E F C V P : Type v}
    {Root : RelStructure L H}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {D : RelStructure L V}
    {A : RelStructure L P}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    [Fintype C] [Fintype E] [Fintype F]
    [Finite V] [Finite P]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hMax : USize rules Whole = Fintype.card C)
    (hDClosed : IsUClosed rules D)
    (hAK : K A) (hAClosed : IsUClosed rules A)
    (q : H → P)
    (pL : E → V) (pR : F → V)
    (hpL : Left.IsHomomorphismEmbedding D pL)
    (hpR : Right.IsHomomorphismEmbedding D pR)
    (aL aR : Embedding A D)
    (hRootL : ∀ r : H, pL (sL r) = aL (q r))
    (hRootR : ∀ r : H, pR (sR r) = aR (q r))
    (j : ℕ)
    (hCardL : Fintype.card E ≤ j)
    (hCardR : Fintype.card F ≤ j)
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
    intro T hFiniteT hT hSize
    letI : Fintype T := hFiniteT
    exact (inducedClosedKCompletion_iff_abstract_2019).mp
      (hRank T hT hSize)
  have hResult : HasClosedUKCompletion K rules Whole :=
    HasClosedUKCompletion.of_maximal_weak_two_ordinary_side_maps_via_A
      rules hStrong hHer hKIrr hSrc hMax hDClosed hAK hAClosed
      q pL pR hpL hpR aL aR hRootL hRootR
      j hCardL hCardR hAbstractRank
  exact (inducedClosedKCompletion_iff_abstract_2019).mpr hResult

/-- The SAME corrected completion conclusion for an actual PROPER
weak free cut of a source on at most j+1 vertices. Source-side
cardinal budgets now follow by elementary finite arithmetic, not
by a false assertion about the size of closed boundary hulls.

The unresolved root-factorization and two ordinary-map hypotheses
are still explicit and indispensable. -/
theorem inducedClosed2019_maximal_proper_weak_cut_via_A
    {K : StructureClass.{u,v} (L := L)}
    (rules : ClosureDescription L)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {Z : Type v} (T : RelStructure L Z),
      K T → T.Irreducible)
    {H E F C V P : Type v}
    {Root : RelStructure L H}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {D : RelStructure L V}
    {A : RelStructure L P}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    [Fintype C] [Fintype E] [Fintype F]
    [Finite V] [Finite P]
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hMax : USize rules Whole = Fintype.card C)
    (hDClosed : IsUClosed rules D)
    (hAK : K A) (hAClosed : IsUClosed rules A)
    (q : H → P)
    (pL : E → V) (pR : F → V)
    (hpL : Left.IsHomomorphismEmbedding D pL)
    (hpR : Right.IsHomomorphismEmbedding D pR)
    (aL aR : Embedding A D)
    (hRootL : ∀ r : H, pL (sL r) = aL (q r))
    (hRootR : ∀ r : H, pR (sR r) = aR (q r))
    (j : ℕ)
    (hTotal : Fintype.card C ≤ j + 1)
    (hProperL : Fintype.card E < Fintype.card C)
    (hProperR : Fintype.card F < Fintype.card C)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (D.induce T) →
      USize rules (D.induce T) ≤ j →
        HasInducedClosedUKCompletion K rules (D.induce T)) :
    HasInducedClosedUKCompletion K rules Whole := by
  apply inducedClosed2019_maximal_weak_two_ordinary_side_maps_via_A
    rules hStrong hHer hKIrr hSrc hMax hDClosed hAK hAClosed
    q pL pR hpL hpR aL aR hRootL hRootR
    j (by omega) (by omega) hRank

end AllThoseRamseyClasses.Published
