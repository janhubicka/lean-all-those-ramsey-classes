import AllThoseRamseyClasses.Published.InducedClosed2019MaximalWeakTwoSide
import PartiteConstruction.Ramsey.ClosureMaximalWeakImageTransfer

/-!
# Exact weak-size 2019 induction: complete BOTH small sides without old rank-j

The corrected j->j+1 weak-vertex-size Picture iteration (PR #133) retains
only completions of ALL exact weak induced old-Picture tests of cardinal at
most j. Earlier two-side gluing (PR #130) instead assumes the STRICTLY
STRONGER closed generating-rank-j invariant. This mismatch is ATRC-020.

This file verifies a genuine useful part of the weaker route.

For any finite exact weak source F of maximal U-size |F| <= j+1, any
PROPER relational free decomposition of F has two sides of at most j
vertices. Each side is again of maximal U-size, hence every ORDINARY
homomorphism-embedding of that side to Old is also protected on closed
U-irreducible tests. Completability of exact weak j-vertex substructures
of Old therefore suffices to give a corrected K-completion of EACH
original exact weak side: factor through its finite image of <=j vertices.

Neither weak side is replaced by its (potentially much larger) ambient
U-closed hull. No closed-rank-j premise, closedness of Old, or common
map on the entire F is needed.

Still MISSING for the native mixed-history step: arrange these two
separately obtained K-completions to agree on one generated closed
K-boundary. Arbitrary completions of the two weak image sets do NOT
automatically preserve an A-copy, even when the ordinary side maps
have compatible A-root factorizations. This declaration proves
individual completability, NOT the free union's completion, the
unconditional Picture increment, or repaired Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Weak-size j completions of Old imply corrected completions of BOTH
actual induced sides of a PROPER free split of an exact maximal-U-rank
source on at most j+1 vertices.

The side projections are only ordinary homomorphism-embeddings,
possibly noninjective on the whole side. No root gluing is claimed. -/
theorem inducedClosed2019_maximal_proper_weak_cut_two_side_completions
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {C V : Type v}
    [Fintype C] [Finite V]
    (Whole : RelStructure L C)
    (hMax : USize rules Whole = Fintype.card C)
    (d : ProperFreeDecomposition Whole)
    (Old : RelStructure L V)
    (pL : d.Left → V) (pR : d.Right → V)
    (hpL : d.left.IsHomomorphismEmbedding Old pL)
    (hpR : d.right.IsHomomorphismEmbedding Old pR)
    (j : ℕ)
    (hTotal : Fintype.card C ≤ j+1)
    (hOldWeak : ∀ T : Finset V, T.card ≤ j →
      HasInducedClosedUKCompletion K rules
        (Old.induce (↑T : Set V))) :
    HasInducedClosedUKCompletion K rules d.left ∧
    HasInducedClosedUKCompletion K rules d.right := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Finite d.Left :=
    Finite.of_injective d.leftIn d.leftIn.injective
  letI : Finite d.Right :=
    Finite.of_injective d.rightIn d.rightIn.injective
  letI : Fintype d.Left := Fintype.ofFinite d.Left
  letI : Fintype d.Right := Fintype.ofFinite d.Right
  have hLessL : Fintype.card d.Left < Fintype.card C :=
    Fintype.card_lt_of_injective_not_surjective
      d.leftIn d.leftIn.injective d.leftProper
  have hLessR : Fintype.card d.Right < Fintype.card C :=
    Fintype.card_lt_of_injective_not_surjective
      d.rightIn d.rightIn.injective d.rightProper
  have hSmallL : Fintype.card d.Left ≤ j := by omega
  have hSmallR : Fintype.card d.Right ≤ j := by omega
  have hMaxL : USize rules d.left = Fintype.card d.Left :=
    Embedding.USize_eq_card_of_embedding_into_maximal hMax d.leftIn
  have hMaxR : USize rules d.right = Fintype.card d.Right :=
    Embedding.USize_eq_card_of_embedding_into_maximal hMax d.rightIn
  have hOldWeakAbstract : ∀ T : Finset V, T.card ≤ j →
      HasClosedUKCompletion K rules (Old.induce (↑T : Set V)) := by
    intro T hT
    exact (inducedClosedKCompletion_iff_abstract_2019).mp
      (hOldWeak T hT)
  have hLeftCompletion : HasClosedUKCompletion K rules d.left :=
    HasClosedUKCompletion.of_maximal_rank_ordinaryHE_weakImage
      pL hpL hMaxL j hSmallL hOldWeakAbstract
  have hRightCompletion : HasClosedUKCompletion K rules d.right :=
    HasClosedUKCompletion.of_maximal_rank_ordinaryHE_weakImage
      pR hpR hMaxR j hSmallR hOldWeakAbstract
  exact ⟨(inducedClosedKCompletion_iff_abstract_2019).mpr
    hLeftCompletion,
    (inducedClosedKCompletion_iff_abstract_2019).mpr
      hRightCompletion⟩

end AllThoseRamseyClasses.Published
