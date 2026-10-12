import AllThoseRamseyClasses.Published.NativeActiveNoCommonCut2019
import AllThoseRamseyClasses.Published.NativeActiveCommonWeakCollision2019
import AllThoseRamseyClasses.Published.NativeZeroActiveCoreCompletion2019

/-!
# Actual 2019 Hales--Jewett weak test: a genuine finite-history TRICHOTOMY

The repaired 2019 higher-rank Picture construction must analyze each
original exact weak source in the TRUE native attachment, not in a
fictitious ideal partite structure or after taking its closed hull.

From the FINITE set T of all private-active source copy indices:

* If T is empty, the source is entirely in the native power core,
  and has an actual corrected completion into selected A∈K.
* If T has one common Hales--Jewett parameter coordinate, the source
  has an actual ORDINARY map to the previous Old Picture. If this
  map has any vertex collision, the source has a corrected completion
  from only the previous exact weak-size W_j(Old) invariant. Otherwise
  retain the ACTUAL injective Old map as a certificate.
* If T has no common coordinate, T contains at least two indices
  (each is an actual PRIVATE exterior index), giving a PROPER exact
  free source decomposition into two sides of at most j vertices.

This is a COMPLETELY REAL finite-case reduction at maximal intrinsic
U-size |Source| <= j+1. The full native attaching language, intermediate
target non-semiclosedness, and noninjective protected projections are
handled by the earlier checked lemmas.

It does NOT assume a proper free split exists in the injective
common-coordinate case; it does not derive any two compatible A-root
maps for the transverse case; and it does not handle nonmaximal-rank
weak sources. No unconditional repaired Theorem 2.18 is asserted.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment
open StructuralRamsey.Partite
open StructuralRamsey.Partite.Induced
open StructuralRamsey.HalesJewett

universe u v
variable {L : RelLanguage.{u}}

/-- Exact maximal-U-rank source on at most j+1 vertices in the TRUE
native attachment: either it already has a corrected K-completion,
or it has an ORDINARY INJECTIVE old-Picture homomorphism-embedding,
or it has a genuine proper relational free split with BOTH exact
source sides of at most j vertices.

The old-Picture completion assumption is W_j only, and is used
only in the real common-coordinate collision branch. No global HJ
coordinate or closed-hull rank-j induction invariant is assumed. -/
theorem native2019_actual_active_weaksize_trichotomy
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {P Q V U I : Type v} {N : ℕ}
    [Fintype U] [Finite Q] [Finite V]
    (Source : RelStructure L U)
    (hMax : USize rules Source = Fintype.card U)
    (Old : System L P V)
    (alpha : Q ↪ P) (A : RelStructure L Q)
    (hAK : K A) (hAIrred : A.Irreducible)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power (Old.restrict alpha) N).toRelStructure A
      (power (Old.restrict alpha) N).part)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (p : U → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I))
    (hp : Source.IsHomomorphismEmbedding
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p)
    (j : ℕ) (hCard : Fintype.card U ≤ j + 1)
    (hOldWeak : ∀ T : Finset V, T.card ≤ j →
      HasInducedClosedUKCompletion K rules
        (Old.toRelStructure.induce (↑T : Set V))) :
    HasInducedClosedUKCompletion K rules Source ∨
      (∃ q : U → V,
        Source.IsHomomorphismEmbedding Old.toRelStructure q ∧
        Function.Injective q) ∨
      (∃ d : ProperFreeDecomposition Source,
        Nat.card d.Left ≤ j ∧ Nat.card d.Right ≤ j) := by
  classical
  let Support := Old.support alpha
  let Core := (power (Old.restrict alpha) N).toRelStructure
  let maps := closureLineMaps Old alpha A hRestricted lines
  let T : Finset I := native2019_exact_active_index_finset Support p
  by_cases hEmpty : T = ∅
  · left
    have hNoPrivate : ∀ x : U, ∀ i : I,
        ¬ OutsideAt (W := NonInduced.Vertex (Old.restrict alpha) N)
          (I := I) Support i (p x) := by
      intro x i hout
      have hi : i ∈ T :=
        (native2019_mem_exact_active_index_iff Support p i).mpr
          ⟨x, hout⟩
      simp [hEmpty] at hi
    exact native2019_maximal_weak_zero_active_has_A_completion
      Source hMax Old alpha A hAK hAIrred
      hPower hRestricted lines p hp hNoPrivate
  · have hT : T.Nonempty := by
      exact Finset.nonempty_iff_ne_empty.mpr hEmpty
    by_cases hCommon : ∃ k : Fin N,
        ∀ i ∈ T, (lines i).symbol k = .parameter
    · obtain ⟨k, hk⟩ := hCommon
      have hActiveCommon : ∀ i : I,
          (∃ x : U, OutsideAt
            (W := NonInduced.Vertex (Old.restrict alpha) N)
            (I := I) Support i (p x)) →
          (lines i).symbol k = .parameter := by
        intro i hi
        exact hk i
          ((native2019_mem_exact_active_index_iff Support p i).mpr hi)
      obtain ⟨q, hq⟩ :=
        native2019_actual_active_common_coordinate_old_ordinary
          Source Old alpha A hRestricted lines p hp k hActiveCommon
      by_cases hInj : Function.Injective q
      · exact Or.inr (Or.inl ⟨q, hq, hInj⟩)
      · have hCollision :
            ∃ x y : U, x ≠ y ∧ q x = q y := by
          by_contra hNone
          have hActuallyInj : Function.Injective q := by
            intro x y hEq
            by_contra hne
            exact hNone ⟨x, y, hne, hEq⟩
          exact hInj hActuallyInj
        obtain ⟨x, y, hxy, heq⟩ := hCollision
        left
        exact inducedClosed2019_maximal_weak_ordinary_collision_of_Wj
          Source Old.toRelStructure hMax q hq j hCard
          x y hxy heq hOldWeak
    · right
      right
      exact native2019_exact_active_no_common_small_free_cut
        Source Old.toRelStructure Support Core maps
        p hp.1 lines j hCard hT hCommon

end AllThoseRamseyClasses.Published
