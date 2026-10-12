import AllThoseRamseyClasses.Published.InducedClosed2019MaximalWeakTwoSide
import PartiteConstruction.Ramsey.ClosureRelativeMapGlue
import PartiteConstruction.Ramsey.ClosureMaximalWeakRankHereditary

/-!
# Direct exact-WEAK-size gluing over a boundary already in the small images

ATRC-020 exposes an important quantifier mismatch: the old two-side
gluing theorem uses completions of CLOSED rank-j target hulls, whereas
the proposed 2019 exact weak-size iteration preserves only completions
of ALL exact weak target subsets of at most j VERTICES.

Here is a proved direct weak-size alternative, with an EXPLICIT stronger
geometry hypothesis rather than a fabricated hull-to-seed implication:

  * the exact maximal-U-rank source is a free amalgam of two induced
    sides, each mapped ordinarily into Old;
  * choose two weak Old target vertex sets TL, TR of cardinal <=j,
    containing ALL the respective source-side images;
  * there is ONE CLOSED irreducible K-boundary Q with TWO genuine
    induced embeddings Q into the WEAK induced substructures Old|TL,
    Old|TR, and the original source-root maps agree via ONE q:Root->Q;
  * the previous Picture has K-completions of ALL exact weak target
    vertex sets of size <=j.

These hypotheses give a genuine K-completion of the WHOLE exact weak
free source. No closed target hulls, closed-rank-j induction premise,
or globally injective/protected projection is used. The side maps are
protected by the maximal rank of the exact source; the relative-source
strong amalgamation lemma then glues the weak target completions over Q.

This does NOT solve the general problem: native A-boundary data from a
constant coordinate currently put Q inside the CLOSED hull of each
side image, not necessarily inside the <=j-vertex weak image itself.
That extra image containment (or another way to extend weak
completions while preserving Q) is the remaining serious obstruction.
The repaired general Theorem 2.18 is NOT claimed.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Weak-j completable old target and an explicitly embedded CLOSED
K-boundary in BOTH SMALL EXACT WEAK OLD SIDE IMAGES give a corrected
K-completion of the entire maximal-U-rank free source.

The two old-side homomorphism-embeddings may be distinct. Target
weak sets and common source root are never replaced with closures. -/
theorem inducedClosed2019_maximal_weak_cut_glue_of_small_weak_boundary
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {H E F C V P : Type v}
    {Root : RelStructure L H}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {Old : RelStructure L V}
    {Q : RelStructure L P}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    [Fintype C] [Fintype E] [Fintype F]
    [Fintype V] [Finite P]
    (hStrong : HasFiniteStrongAmalgamation K)
    (hKIrr : ∀ {X : Type v} (T : RelStructure L X),
      K T → T.Irreducible)
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hMax : USize rules Whole = Fintype.card C)
    (pL : E → V) (pR : F → V)
    (hpL : Left.IsHomomorphismEmbedding Old pL)
    (hpR : Right.IsHomomorphismEmbedding Old pR)
    (hQK : K Q) (hQClosed : IsUClosed rules Q)
    (TL TR : Finset V)
    (hRangeL : ∀ x : E, pL x ∈ TL)
    (hRangeR : ∀ x : F, pR x ∈ TR)
    (q : H → P)
    (aL : Embedding Q (Old.induce (↑TL : Set V)))
    (aR : Embedding Q (Old.induce (↑TR : Set V)))
    (hRootL : ∀ r : H, pL (sL r) = (aL (q r)).1)
    (hRootR : ∀ r : H, pR (sR r) = (aR (q r)).1)
    (j : ℕ) (hSizeL : TL.card ≤ j) (hSizeR : TR.card ≤ j)
    (hOldWeak : ∀ T : Finset V, T.card ≤ j →
      HasInducedClosedUKCompletion K rules
        (Old.induce (↑T : Set V))) :
    HasInducedClosedUKCompletion K rules Whole := by
  classical
  have hRelL : IsUSubstructure rules Whole (Set.range iL) :=
    all_subsets_relative_of_USize_eq_card rules Whole hMax
      (Set.range iL)
  have hRelR : IsUSubstructure rules Whole (Set.range iR) :=
    all_subsets_relative_of_USize_eq_card rules Whole hMax
      (Set.range iR)
  have hMaxL : USize rules Left = Fintype.card E :=
    Embedding.USize_eq_card_of_embedding_into_maximal hMax iL
  have hMaxR : USize rules Right = Fintype.card F :=
    Embedding.USize_eq_card_of_embedding_into_maximal hMax iR
  have hProtectedL : IsClosedUHomomorphismEmbedding rules Left Old pL :=
    hpL.toClosedMap_of_max_USize hMaxL
  have hProtectedR : IsClosedUHomomorphismEmbedding rules Right Old pR :=
    hpR.toClosedMap_of_max_USize hMaxR
  let gL : E → (↑TL : Set V) :=
    fun x => ⟨pL x, hRangeL x⟩
  let gR : F → (↑TR : Set V) :=
    fun x => ⟨pR x, hRangeR x⟩
  have hgL : IsClosedUHomomorphismEmbedding rules
      Left (Old.induce (↑TL : Set V)) gL :=
    hProtectedL.codRestrict (↑TL : Set V) hRangeL
  have hgR : IsClosedUHomomorphismEmbedding rules
      Right (Old.induce (↑TR : Set V)) gR :=
    hProtectedR.codRestrict (↑TR : Set V) hRangeR
  have hCompatL (r : H) : gL (sL r) = aL (q r) := by
    apply Subtype.ext
    exact hRootL r
  have hCompatR (r : H) : gR (sR r) = aR (q r) := by
    apply Subtype.ext
    exact hRootR r
  have hDL : HasClosedUKCompletion K rules
      (Old.induce (↑TL : Set V)) :=
    (inducedClosedKCompletion_iff_abstract_2019).mp
      (hOldWeak TL hSizeL)
  have hDR : HasClosedUKCompletion K rules
      (Old.induce (↑TR : Set V)) :=
    (inducedClosedKCompletion_iff_abstract_2019).mp
      (hOldWeak TR hSizeR)
  have hFinal : HasClosedUKCompletion K rules Whole :=
    HasClosedUKCompletion.of_independent_projected_completions_relative
      rules hStrong hKIrr hFree hRelL hRelR
      Q hQK hQClosed
      (Old.induce (↑TL : Set V))
      (Old.induce (↑TR : Set V))
      gL gR hgL hgR q aL aR hCompatL hCompatR hDL hDR
  exact (inducedClosedKCompletion_iff_abstract_2019).mpr hFinal

end AllThoseRamseyClasses.Published
