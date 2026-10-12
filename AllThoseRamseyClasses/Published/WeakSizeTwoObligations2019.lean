import AllThoseRamseyClasses.Published.ExactWeakBoundaryGluing2019
import PartiteConstruction.Ramsey.ClosureWeakIrreducibleCoverage

/-!
# Corrected 2019 Lemma 2.30: an EXACT W_j -> W_(j+1) conditional interface

ATRC-020 records a *real* invariant mismatch. The earlier geometric
induction lemmas #135/#139 demand R_j(D): completion of all closed
substructures of generating rank <=j. The actual weak-size tower #133
only preserves W_j(D): completion of ALL exact weak induced j-vertex
substructures. R_j cannot be recovered by completing minimum generators
(upstream PR #234 gives a finite adversarial counterexample).

Here we prove a corrected CONDITIONAL exact weak-size increment with
only W_j(D), using #145's genuine weak-target A-boundary gluing. Its
unproved inputs are stated at their true scopes, in TWO distinct cases:

  (1) each non-MAXIMAL-U-rank weak test F on <=j+1 vertices already has
      a corrected K-completion (no illegal generator-to-hull extension);
  (2) each MAXIMAL-U-rank, ordinary reducible weak test has ONE selected
      PROPER relational free source decomposition, ordinary old-Picture
      side maps, and a SINGLE closed A in K with induced embeddings into
      TWO actual WEAK OLD target sets TL,TR of <=j vertices.

Ordinary irreducible weak tests are already completable from coverage
of closed U-irreducible tests by an irreducible B in K (#215). In the
maximal reducible case, #145 genuinely glues the two weak-image
completions over A, with no R_j hypothesis anywhere.

The result has the exact W_j input and W_(j+1) output needed by #133,
but does not construct either universal native hypothesis (1)/(2).
In particular, obtaining A in the SMALL weak target image is stronger
than merely locating A in the closure of that image.

No unconditional general repaired Theorem 2.18 is asserted.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- A sufficient history certificate for a MAXIMAL rank exact weak
REDUCIBLE test: choose ONE actual source free split and two ordinary
Old maps; both small weak Old target vertex sets must already contain
induced embeddings of the SAME A, compatible with one root q.

No all-decompositions quantifier; no completion of a larger closed
target hull, and no closure assumption on the original weak test. -/
def Has2019SelectedSmallWeakABoundaryGeometry
    {VC VD VA : Type v}
    (rules : ClosureDescription L)
    (C : RelStructure L VC)
    (D : RelStructure L VD)
    (A : RelStructure L VA)
    (j : ℕ) : Prop :=
  ∀ (S : Finset VC),
    S.card ≤ j+1 →
    USize rules (C.induce (↑S : Set VC)) = S.card →
    ¬ (C.induce (↑S : Set VC)).Irreducible →
    ∃ d : ProperFreeDecomposition (C.induce (↑S : Set VC)),
      ∃ (TL TR : Finset VD)
        (pL : d.Left → VD) (pR : d.Right → VD)
        (q : d.Common → VA)
        (aL : Embedding A (D.induce (↑TL : Set VD)))
        (aR : Embedding A (D.induce (↑TR : Set VD))),
        TL.card ≤ j ∧ TR.card ≤ j ∧
        (∀ x : d.Left, pL x ∈ TL) ∧
        (∀ x : d.Right, pR x ∈ TR) ∧
        d.left.IsHomomorphismEmbedding D pL ∧
        d.right.IsHomomorphismEmbedding D pR ∧
        (∀ r : d.Common, pL (d.toLeft r) = (aL (q r)).1) ∧
        (∀ r : d.Common, pR (d.toRight r) = (aR (q r)).1)

/-- The W_j(D) invariant is preserved across THIS corrected weak-size
step if both genuinely missing branches are provided explicitly.

Unlike the older closed-rank proof, hOldWeak is the only old-Picture
completion hypothesis; the nonmaximal-rank case is NOT assumed to
follow from W_j, and the maximal reducible gluing requires a common
A already inside each small exact weak target. -/
theorem inducedClosed2019_weaksize_increment_of_nonmax_and_small_weak_A_geometry
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {VC VD VA VB : Type v}
    [Finite VC] [Finite VD] [Finite VA] [Finite VB]
    (C : RelStructure L VC)
    (D : RelStructure L VD)
    (A : RelStructure L VA)
    (B : RelStructure L VB)
    (hC : IsUClosed rules C)
    (hStrong : HasFiniteStrongAmalgamation K)
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
    (hOldWeak : ∀ T : Finset VD, T.card ≤ j →
      HasInducedClosedUKCompletion K rules
        (D.induce (↑T : Set VD)))
    (hNonmax : ∀ S : Finset VC, S.card ≤ j+1 →
      USize rules (C.induce (↑S : Set VC)) ≠ S.card →
      HasInducedClosedUKCompletion K rules
        (C.induce (↑S : Set VC)))
    (hGeometry :
      Has2019SelectedSmallWeakABoundaryGeometry rules C D A j) :
    ∀ S : Finset VC, S.card ≤ j+1 →
      HasInducedClosedUKCompletion K rules
        (C.induce (↑S : Set VC)) := by
  classical
  letI : Fintype VC := Fintype.ofFinite VC
  letI : Fintype VD := Fintype.ofFinite VD
  intro S hCard
  by_cases hMax :
      USize rules (C.induce (↑S : Set VC)) = S.card
  · by_cases hIrred : (C.induce (↑S : Set VC)).Irreducible
    · have hAbs :=
        weak_irreducible_completion_of_closed_coverage
          hC hBK hBIrred hCover (↑S : Set VC) hIrred
      exact (inducedClosedKCompletion_iff_abstract_2019).mpr hAbs
    · obtain ⟨d, TL, TR, pL, pR, q, aL, aR,
          hSizeL, hSizeR, hRangeL, hRangeR, hpL, hpR,
          hRootL, hRootR⟩ :=
        hGeometry S hCard hMax hIrred
      letI : Finite d.Left :=
        Finite.of_injective d.leftIn d.leftIn.injective
      letI : Finite d.Right :=
        Finite.of_injective d.rightIn d.rightIn.injective
      letI : Fintype d.Left := Fintype.ofFinite d.Left
      letI : Fintype d.Right := Fintype.ofFinite d.Right
      have hMaxCard :
          USize rules (C.induce (↑S : Set VC)) =
            Fintype.card (↑S : Set VC) := by
        simpa using hMax
      exact inducedClosed2019_maximal_weak_cut_glue_of_small_weak_boundary
        hStrong hKIrr d.free hMaxCard
        pL pR hpL hpR hAK hAClosed
        TL TR hRangeL hRangeR q aL aR hRootL hRootR
        j hSizeL hSizeR hOldWeak
  · exact hNonmax S hCard hMax

end AllThoseRamseyClasses.Published
