import AllThoseRamseyClasses.Published.InducedClosed2019WeakGeometricReduction

/-!
# 2019 corrected exact weak-size promotion with SELECTED native free-cut geometry

The existing geometric interface Has2019MaximalWeakGeometricCertificates
demands A-compatible side maps on EVERY proper free decomposition of a maximal
weak tested source. That is unnecessarily strong for the actual Hales--Jewett
proof: a native attachment offers a PARTICULAR copy/rest cut.

This file proves that the entire corrected j->j+1 weak-test promotion only
needs ONE SELECTED proper free cut, whenever the source has maximal U-size
and SOME proper free cut exists. The previous verified exact-weak dichotomy
supplies this nonemptiness in precisely the outstanding case. The selection
must include actual side vertex bounds and two old-Picture ordinary maps
whose roots factor through the SAME q into closed A.

The missing native theorem must therefore construct an existential witness,
not a family uniformly covering arbitrary decompositions. No general native
witness or unconditional repaired Theorem 2.18 is postulated.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- The history must select a GOOD actual proper free decomposition of each
maximal weak source for which a free decomposition exists. Its two sides
have absolute vertex bounds <= j and are A-compatible inside Old.

No all-decomposition quantifier is imposed. The exact weak source is never
replaced with a closure hull. This is the remaining conditional interface. -/
def Has2019SelectedMaximalWeakGeometricCertificates
    {VC VD VA : Type v}
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (C : RelStructure L VC)
    (D : RelStructure L VD)
    (A : RelStructure L VA)
    (j : ℕ) : Prop :=
  ∀ (S : Finset VC),
    USize rules (C.induce (↑S : Set VC)) = S.card →
    Nonempty (ProperFreeDecomposition (C.induce (↑S : Set VC))) →
    ∃ d : ProperFreeDecomposition (C.induce (↑S : Set VC)),
      Nat.card d.Left ≤ j ∧
      Nat.card d.Right ≤ j ∧
      ∃ (q : d.Common → VA)
        (pL : d.Left → VD) (pR : d.Right → VD)
        (aL aR : Embedding A D),
        d.left.IsHomomorphismEmbedding D pL ∧
        d.right.IsHomomorphismEmbedding D pR ∧
        (∀ r : d.Common, pL (d.toLeft r) = aL (q r)) ∧
        (∀ r : d.Common, pR (d.toRight r) = aR (q r))

/-- Relative to the existing repaired 2019 contracts and rank-j assumption,
the SELECTED rather than all-decomposition native A-geometry suffices for
every exact induced weak source on <= j+1 vertices.

The old rank-j invariant is transferred only across CLOSED tests; the
unclosed source is kept exact in the weak-size dichotomy and gluing. -/
theorem inducedClosed2019_weaksize_increment_of_selected_A_compatible_geometry
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
      Has2019SelectedMaximalWeakGeometricCertificates K rules C D A j) :
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
  -- The dichotomy gives SOME nontrivial free decomposition; unlike
  -- the earlier universal geometry contract, we now ask the native
  -- history to SELECT ONE suitable decomposition of this exact test.
  obtain ⟨dSelected, hSideL, hSideR,
      q, pL, pR, aL, aR, hpL, hpR, hRootL, hRootR⟩ :=
    hGeometry S hMaxS ⟨d⟩
  letI : Finite dSelected.Left :=
    Finite.of_injective dSelected.leftIn dSelected.leftIn.injective
  letI : Finite dSelected.Right :=
    Finite.of_injective dSelected.rightIn dSelected.rightIn.injective
  letI : Fintype dSelected.Left := Fintype.ofFinite dSelected.Left
  letI : Fintype dSelected.Right := Fintype.ofFinite dSelected.Right
  have hMax :
      USize rules (C.induce (↑S : Set VC)) =
        Fintype.card (↑S : Set VC) := by
    simpa using hMaxS
  have hSmallL : Fintype.card dSelected.Left ≤ j := by
    simpa only [Nat.card_eq_fintype_card] using hSideL
  have hSmallR : Fintype.card dSelected.Right ≤ j := by
    simpa only [Nat.card_eq_fintype_card] using hSideR
  exact inducedClosed2019_maximal_weak_two_ordinary_side_maps_via_A
    rules hStrong hHer hKIrr dSelected.free hMax
    hD hAK hAClosed
    q pL pR hpL hpR aL aR hRootL hRootR
    j hSmallL hSmallR hOldRank

end AllThoseRamseyClasses.Published
