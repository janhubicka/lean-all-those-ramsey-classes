import AllThoseRamseyClasses.Published.InducedClosed2019RankPreservation
import AllThoseRamseyClasses.Published.InducedClosed2019MaximalWeakTwoSide
import PartiteConstruction.Ramsey.ClosureWeakSmallFreeCut

/-!
# 2019 Lemma 2.30: reduce EXACT weak-size promotion to native A-root geometry

The repaired Definition 2.17(4c) tests EVERY exact induced weak source on
at most n VERTICES. The original Lemma 2.30 seeks a stronger invariant
on U-closed sources of bounded intrinsic generating rank. Those are not
interchangeable: a completion of an exact weak minimum-generator seed
need not extend over its prescribed closed hull (the finite adversarial
counterexample is documented in the upstream partite-construction
repository, merged PR #234).

Here we prove a genuine, more precisely targeted conditional result.

Suppose C is a finite U-closed picture, protected under the corrected
2019 map into a finite U-closed OLD picture D. Suppose every closed
induced rank-j test in D has its corrected K-completion, and every
closed irreducible test in C embeds into one original irreducible
B∈K (the stronger B-copy coverage produced by native Picture passes).

The old rank-j premise transfers through the protected projection to
C. The upstream exact weak-size structural dichotomy then proves:
  - either any given weak test S of at most j+1 vertices is already
    completable; or
  - S has maximal U-size and a PROPER relational free decomposition
    into two induced sides with at most j vertices each.

In the latter branch, the pinned maximal-rank gluing theorem requires
ONLY two (possibly different) ORDINARY side homomorphism-embeddings
into D which factor their common root through TWO embeddings of one
fixed closed A∈K. No single global projection on the source, U-closed
root, or ad hoc root-K-completion is required. The closed K-boundary is
constructed by taking the root image's generated hull INSIDE A.

The entire theorem below discharges the weak-size j+1 completion
obligation from exactly that EXPLICIT A-compatible side-map geometry,
using the paper-faithful induced closed-test completion convention.

Still MISSING (not asserted by this theorem): prove that the ACTUAL
native multi-line Hales--Jewett history supplies the two A-compatible
side maps for the relevant free cut. CI-green PRs #125, #128, #129,
#131 and #132 construct partial candidate retractions and A-boundary
factorizations, but none establishes the full universal case.

No global Ramsey theorem or unsupplied Picture increment is claimed.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- A sufficient geometric certificate for an exact small weak test:
for each proper free decomposition at MAXIMAL intrinsic U-size, the
two source sides have ordinary maps into the SAME old picture D, and
their common root factors through two copies of the SAME A in D.

The condition is intentionally not an assertion that native Pictures
always provide such a certificate: that assertion is precisely the
remaining true Hales--Jewett history lemma. -/
def Has2019MaximalWeakGeometricCertificates
    {VC VD VA : Type v}
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (C : RelStructure L VC)
    (D : RelStructure L VD)
    (A : RelStructure L VA)
    (j : ℕ) : Prop :=
  ∀ (S : Finset VC)
    (d : ProperFreeDecomposition (C.induce (↑S : Set VC))),
    USize rules (C.induce (↑S : Set VC)) = S.card →
    ∃ (q : d.Common → VA)
      (pL : d.Left → VD) (pR : d.Right → VD)
      (aL aR : Embedding A D),
      d.left.IsHomomorphismEmbedding D pL ∧
      d.right.IsHomomorphismEmbedding D pR ∧
      (∀ r : d.Common, pL (d.toLeft r) = aL (q r)) ∧
      (∀ r : d.Common, pR (d.toRight r) = aR (q r))

/-- The exact weak-size j->j+1 COMPLETION claim follows from the
old U-closed rank-j invariant and explicitly certified
A-compatible maximal-rank free cuts.

The original test is C|S throughout; it is never enlarged to
its ambient closure. Every possible source-side and shared root
may be nonclosed. The side size budgets are derived from a PROPER
free cut, not guessed by subtracting closure generators. -/
theorem inducedClosed2019_weaksize_increment_of_A_compatible_geometry
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {VC VD VA VB : Type v}
    [Finite VC] [Finite VD] [Finite VA] [Finite VB]
    (C : RelStructure L VC)
    (D : RelStructure L VD)
    (A : RelStructure L VA)
    (B : RelStructure L VB)
    (hC : IsUClosed rules C)
    (hD : IsUClosed rules D)
    (p : VC → VD)
    (hp : IsInducedClosedUHomomorphismEmbedding rules C D p)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {Z : Type v} (T : RelStructure L Z),
      K T → T.Irreducible)
    (hAK : K A) (hAClosed : IsUClosed rules A)
    (hBK : K B) (hBIrred : B.Irreducible)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test →
      IsUIrreducible rules Test →
      Embedding Test C →
      Nonempty (Embedding Test B))
    (j : ℕ)
    (hOldRank : ∀ (T : Set VD) [Fintype T],
      IsUClosed rules (D.induce T) →
      USize rules (D.induce T) ≤ j →
      HasInducedClosedUKCompletion K rules (D.induce T))
    (hGeometry :
      Has2019MaximalWeakGeometricCertificates K rules C D A j) :
    ∀ S : Finset VC, S.card ≤ j+1 →
      HasInducedClosedUKCompletion K rules
        (C.induce (↑S : Set VC)) := by
  classical
  have hpAbstract :
      IsClosedUHomomorphismEmbedding rules C D p :=
    IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hp
  have hRankC :
      ∀ (T : Set VC) [Fintype T],
        IsUClosed rules (C.induce T) →
        USize rules (C.induce T) ≤ j →
        HasClosedUKCompletion K rules (C.induce T) := by
    intro T hFT _ hSize
    letI : Fintype T := hFT
    have hpT :
        IsInducedClosedUHomomorphismEmbedding rules
          (C.induce T) D (p ∘ Subtype.val) :=
      IsClosedUHomomorphismEmbedding.toInducedClosed
        (hpAbstract.precomp_embedding (inclusion C T))
    exact (inducedClosedKCompletion_iff_abstract_2019).mp
      (inducedClosed2019_completion_of_bounded_rank_projection
        hD hpT j hOldRank hSize)
  intro S hCard
  rcases weak_test_complete_or_small_relative_free_cut
      C B hC hBK hBIrred hCover j hRankC S hCard with
      hDone | ⟨d, _, _, hCardL, hCardR⟩
  · exact (inducedClosedKCompletion_iff_abstract_2019).mpr hDone
  rcases weak_test_complete_or_maximal_independent
      C hC j hRankC S hCard with
      hDone | ⟨_, hMaxS, _⟩
  · exact (inducedClosedKCompletion_iff_abstract_2019).mpr hDone
  letI : Finite d.Left :=
    Finite.of_injective d.leftIn d.leftIn.injective
  letI : Finite d.Right :=
    Finite.of_injective d.rightIn d.rightIn.injective
  letI : Fintype d.Left := Fintype.ofFinite d.Left
  letI : Fintype d.Right := Fintype.ofFinite d.Right
  have hMax :
      USize rules (C.induce (↑S : Set VC)) =
        Fintype.card (↑S : Set VC) := by
    simpa using hMaxS
  have hSmallL : Fintype.card d.Left ≤ j := by
    simpa only [Nat.card_eq_fintype_card] using hCardL
  have hSmallR : Fintype.card d.Right ≤ j := by
    simpa only [Nat.card_eq_fintype_card] using hCardR
  obtain ⟨q, pL, pR, aL, aR, hpL, hpR, hRootL, hRootR⟩ :=
    hGeometry S d hMaxS
  exact inducedClosed2019_maximal_weak_two_ordinary_side_maps_via_A
    rules hStrong hHer hKIrr d.free hMax
    hD hAK hAClosed
    q pL pR hpL hpR aL aR hRootL hRootR
    j hSmallL hSmallR hOldRank

end AllThoseRamseyClasses.Published
