import AllThoseRamseyClasses.Applications.PosetPushoutOrderCompatibility
import AllThoseRamseyClasses.Applications.OrderedPosetHereditary
import PartiteConstruction.Ramsey.CompatibleClassCompletion

/-!
# Genuine strong amalgamation of finite ordered posets

This discharges the strong-amalgamation field of the 2019 corrected
class criterion for finite partial orders equipped with a linear
extension. Start with the REAL strong vertex pushout; use the checked
generic compatible-order construction from PR #210; define partial
order comparisons within a side exactly as before and across sides
only when they factor through the shared FULL induced poset root.

Verified component lemmas:
* root-factorized relation reflexive/transitive (#215);
* BOTH side embeddings preserve and reflect it (#215, #216);
* every nontrivial new comparison strictly increases the common
  vertex order, so antisymmetry holds (#217).

The auxiliary `.mate` symbol in the named ambient language remains
empty and introduces no extra combinatorial structure. The target
uses NO new vertex identifications. This is a strong amalgam, not
merely weak amalgamation or a conditional completion.

The corrected 2019 local-completion class instance and Ramsey
transfer remain separate obligations; this module asserts neither.
-/

namespace AllThoseRamseyClasses.Applications.OrderedPosets

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- The actual class of finite ordered posets has strong
amalgamation over its FULL induced ordered-poset substructures. -/
theorem orderedPosetClass_strongAmalgamation :
    HasFiniteStrongAmalgamation orderedPosetClass := by
  intro H E F hFiniteH hFiniteE hFiniteF Root Left Right
    hRoot hLeft hRight sL sR
  classical
  let P := FreeAmalgam.Vertex Root Left Right sL sR
  let C := FreeAmalgam.amalgam Root Left Right sL sR
  let iL := FreeAmalgam.leftEmbedding Root Left Right sL sR
  let iR := FreeAmalgam.rightEmbedding Root Left Right sL sR
  have hP : Finite P := inferInstance
  letI : Finite P := hP
  let hFree : IsFreeAmalgam sL sR iL iR :=
    FreeAmalgam.isFreeAmalgam Root Left Right sL sR
  obtain ⟨o, hOrdL, hOrdR⟩ :=
    ambient_ordered_pushout_exists hFree hLeft.1 hRight.1
  letI : LinearOrder P := o
  let q : P → P → Prop :=
    posetPushoutRelation Root Left Right sL sR
      (edge Left .equiv) (edge Right .equiv)
  have hRootEq : ∀ d e : H,
      edge Left .equiv (sL d) (sL e) ↔
      edge Right .equiv (sR d) (sR e) := by
    intro d e
    exact (edge_embedding_iff sL .equiv d e).trans
      (edge_embedding_iff sR .equiv d e).symm
  have hqRefl : ∀ x : P, q x x :=
    posetPushoutRelation_refl Root Left Right sL sR
      (edge Left .equiv) (edge Right .equiv)
      hLeft.2.1 hRight.2.1
  have hqTrans : ∀ x y z : P,
      q x y → q y z → q x z :=
    posetPushoutRelation_trans Root Left Right sL sR
      (edge Left .equiv) (edge Right .equiv)
      hLeft.2.2.1 hRight.2.2.1 hRootEq
  have hqAnti : ∀ x y : P,
      q x y → q y x → x = y :=
    posetPushoutRelation_antisymm Root Left Right sL sR
      hLeft hRight o hOrdL hOrdR
  have hqOrd : ∀ x y : P,
      x ≠ y → q x y → x < y := by
    intro x y hne hp
    exact posetPushoutRelation_strict_order
      Root Left Right sL sR hLeft hRight o
      hOrdL hOrdR x y hne hp
  let Target : RelStructure Lang P := {
    rel := fun
      | .lt, t => @LT.lt P o.toLT (t 0) (t 1)
      | .equiv, t => q (t 0) (t 1)
      | .mate, _ => False
  }
  have hTarget : orderedPosetClass Target := by
    refine ⟨⟨hP, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hxx
      exact lt_irrefl x hxx
    · intro x y z hxy hyz
      exact lt_trans hxy hyz
    · intro x y hne
      exact lt_or_gt_of_ne hne
    · exact hqRefl
    · exact hqTrans
    · exact hqAnti
    · exact hqOrd
    · intro x y hxy
      exact hxy
  have hOrderLeft (a b : E) :
      (@LT.lt P o.toLT (iL a) (iL b)) ↔
        edge Left .lt a b := by
    constructor
    · intro hab
      by_cases heq : a = b
      · subst b
        exact (lt_irrefl _ hab).elim
      · rcases hLeft.1.2.2.2 a b heq with habOld | hbaOld
        · exact habOld
        · exact (lt_asymm (hOrdL b a hbaOld) hab).elim
    · exact hOrdL a b
  have hOrderRight (a b : F) :
      (@LT.lt P o.toLT (iR a) (iR b)) ↔
        edge Right .lt a b := by
    constructor
    · intro hab
      by_cases heq : a = b
      · subst b
        exact (lt_irrefl _ hab).elim
      · rcases hRight.1.2.2.2 a b heq with habOld | hbaOld
        · exact habOld
        · exact (lt_asymm (hOrdR b a hbaOld) hab).elim
    · exact hOrdR a b
  let jL : Embedding Left Target := {
    toFun := iL
    injective := iL.injective
    map_rel_iff := by
      intro Rel t
      have ht : t = ![t 0, t 1] := by
        funext i
        fin_cases i <;> rfl
      rw [ht]
      cases Rel with
      | lt =>
          change (@LT.lt P o.toLT (iL (t 0)) (iL (t 1))) ↔
            edge Left .lt (t 0) (t 1)
          exact hOrderLeft (t 0) (t 1)
      | equiv =>
          change q (iL (t 0)) (iL (t 1)) ↔
            edge Left .equiv (t 0) (t 1)
          exact posetPushoutRelation_left_iff
            Root Left Right sL sR
              (edge Left .equiv) (edge Right .equiv)
              (t 0) (t 1)
      | mate =>
          change False ↔ edge Left .mate (t 0) (t 1)
          exact (iff_false_intro (hLeft.2.2.2.2.2 (t 0) (t 1))).symm
  }
  let jR : Embedding Right Target := {
    toFun := iR
    injective := iR.injective
    map_rel_iff := by
      intro Rel t
      have ht : t = ![t 0, t 1] := by
        funext i
        fin_cases i <;> rfl
      rw [ht]
      cases Rel with
      | lt =>
          change (@LT.lt P o.toLT (iR (t 0)) (iR (t 1))) ↔
            edge Right .lt (t 0) (t 1)
          exact hOrderRight (t 0) (t 1)
      | equiv =>
          change q (iR (t 0)) (iR (t 1)) ↔
            edge Right .equiv (t 0) (t 1)
          exact posetPushoutRelation_right_iff
            Root Left Right sL sR
              (edge Left .equiv) (edge Right .equiv)
              hLeft.2.1 hRight.2.2.1 hRootEq
              (t 0) (t 1)
      | mate =>
          change False ↔ edge Right .mate (t 0) (t 1)
          exact (iff_false_intro (hRight.2.2.2.2.2 (t 0) (t 1))).symm
  }
  refine ⟨P, hP, Target, hTarget, jL, jR, ?_, ?_⟩
  · exact FreeAmalgam.left_right_overlap Root Left Right sL sR
  · intro a b hab
    exact (hFree.overlap a b).mp hab

end AllThoseRamseyClasses.Applications.OrderedPosets
