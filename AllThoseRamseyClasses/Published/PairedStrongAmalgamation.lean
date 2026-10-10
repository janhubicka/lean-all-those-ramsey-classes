import AllThoseRamseyClasses.Published.EquivalencePushoutRelation
import AllThoseRamseyClasses.Published.OrderedPushoutFromKeys
import AllThoseRamseyClasses.Published.OrderedCompatibleKeys
import AllThoseRamseyClasses.Published.MatchingFreeAmalgamTotal
import AllThoseRamseyClasses.Published.FinitePairedClass

/-!
# Genuine strong amalgamation of finite ordered paired equivalences

This completes the one missing class-theoretic hypothesis needed to
combine the printed 2019 Theorem 2.18 paired-equivalence counterexample.

Construct the EXACT strong vertex pushout with FreeAmalgam.amalgam;
extend its equivalence relation by equality of shared/private class
labels (the side embeddings remain induced); extend its strict linear
order via common root-compatible keys; and preserve its original
perfect matching M. Neither the E-closure nor the new linear order
identifies additional vertices, and both side embeddings reflect
negative relation instances.

This theorem does NOT prove the corrected general Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- A strict order extending a finite linear order on a side must
also REFLECT its order, because the side order is total. -/
private theorem order_reflect_of_strict_mono
    {E P : Type}
    {Left : RelStructure Lang E}
    (hLeft : pairedClass Left)
    (o : LinearOrder P) (f : E → P)
    (hf : ∀ a b : E, edge Left .lt a b →
      @LT.lt P o.toLT (f a) (f b))
    (a b : E) :
    (@LT.lt P o.toLT (f a) (f b)) ↔
      edge Left .lt a b := by
  letI : LinearOrder P := o
  constructor
  · intro hab
    by_cases heq : a = b
    · subst b
      exact (lt_irrefl _ hab).elim
    · rcases hLeft.lt_total a b heq with hlt | hrev
      · exact hlt
      · exact (lt_asymm (hf b a hrev) hab).elim
  · exact hf a b

/-- The free relational amalgam keeps M irreflexive, because every
positive M tuple belongs to one of the original induced sides. -/
private theorem freeAmalgam_mate_irrefl
    {D E F : Type}
    (Root : RelStructure Lang D)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (hLeft : pairedClass Left) (hRight : pairedClass Right)
    (sL : Embedding Root Left) (sR : Embedding Root Right) :
    ∀ x : FreeAmalgam.Vertex Root Left Right sL sR,
      ¬ edge (FreeAmalgam.amalgam Root Left Right sL sR)
          .mate x x := by
  intro x hxx
  let C := FreeAmalgam.amalgam Root Left Right sL sR
  let iL := FreeAmalgam.leftEmbedding Root Left Right sL sR
  let iR := FreeAmalgam.rightEmbedding Root Left Right sL sR
  have hFree := FreeAmalgam.isFreeAmalgam Root Left Right sL sR
  have hTuple : C.rel .mate ![x, x] := hxx
  rcases (hFree.rel_iff .mate ![x, x]).mp hTuple with
      ⟨t, ht, he⟩ | ⟨t, ht, he⟩
  · have hEqImage : iL (t 0) = iL (t 1) :=
      (congrFun he 0).symm.trans (congrFun he 1)
    have hEq : t 0 = t 1 := iL.injective hEqImage
    have hOld : edge Left .mate (t 0) (t 1) := by
      change Left.rel .mate ![t 0, t 1]
      have htup : t = ![t 0, t 1] := by
        funext k
        fin_cases k <;> rfl
      rw [← htup]
      exact ht
    rw [hEq] at hOld
    exact hLeft.mate_irrefl (t 1) hOld
  · have hEqImage : iR (t 0) = iR (t 1) :=
      (congrFun he 0).symm.trans (congrFun he 1)
    have hEq : t 0 = t 1 := iR.injective hEqImage
    have hOld : edge Right .mate (t 0) (t 1) := by
      change Right.rel .mate ![t 0, t 1]
      have htup : t = ![t 0, t 1] := by
        funext k
        fin_cases k <;> rfl
      rw [← htup]
      exact ht
    rw [hEq] at hOld
    exact hRight.mate_irrefl (t 1) hOld

/-- The free amalgam preserves symmetric matching: each M tuple
originates entirely on a single side, where its reverse is present. -/
private theorem freeAmalgam_mate_symm
    {D E F : Type}
    (Root : RelStructure Lang D)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (hLeft : pairedClass Left) (hRight : pairedClass Right)
    (sL : Embedding Root Left) (sR : Embedding Root Right) :
    ∀ x y : FreeAmalgam.Vertex Root Left Right sL sR,
      edge (FreeAmalgam.amalgam Root Left Right sL sR)
          .mate x y →
      edge (FreeAmalgam.amalgam Root Left Right sL sR)
          .mate y x := by
  intro x y hxy
  let C := FreeAmalgam.amalgam Root Left Right sL sR
  let iL := FreeAmalgam.leftEmbedding Root Left Right sL sR
  let iR := FreeAmalgam.rightEmbedding Root Left Right sL sR
  have hFree := FreeAmalgam.isFreeAmalgam Root Left Right sL sR
  have hTuple : C.rel .mate ![x, y] := hxy
  rcases (hFree.rel_iff .mate ![x, y]).mp hTuple with
      ⟨t, ht, he⟩ | ⟨t, ht, he⟩
  · have hOld : edge Left .mate (t 0) (t 1) := by
      change Left.rel .mate ![t 0, t 1]
      have htup : t = ![t 0, t 1] := by
        funext k
        fin_cases k <;> rfl
      rw [← htup]
      exact ht
    have hOldRev : edge Left .mate (t 1) (t 0) :=
      hLeft.mate_symm (t 0) (t 1) hOld
    have hImage : C.rel .mate (iL ∘ ![t 1, t 0]) :=
      (iL.map_rel_iff .mate ![t 1, t 0]).mpr hOldRev
    have hx : x = iL (t 0) := by simpa using congrFun he 0
    have hy : y = iL (t 1) := by simpa using congrFun he 1
    change C.rel .mate ![y, x]
    rw [hx, hy]
    have hRevTuple : ![iL (t 1), iL (t 0)] =
        iL ∘ ![t 1, t 0] := by
      funext k
      fin_cases k <;> rfl
    rw [hRevTuple]
    exact hImage
  · have hOld : edge Right .mate (t 0) (t 1) := by
      change Right.rel .mate ![t 0, t 1]
      have htup : t = ![t 0, t 1] := by
        funext k
        fin_cases k <;> rfl
      rw [← htup]
      exact ht
    have hOldRev : edge Right .mate (t 1) (t 0) :=
      hRight.mate_symm (t 0) (t 1) hOld
    have hImage : C.rel .mate (iR ∘ ![t 1, t 0]) :=
      (iR.map_rel_iff .mate ![t 1, t 0]).mpr hOldRev
    have hx : x = iR (t 0) := by simpa using congrFun he 0
    have hy : y = iR (t 1) := by simpa using congrFun he 1
    change C.rel .mate ![y, x]
    rw [hx, hy]
    have hRevTuple : ![iR (t 1), iR (t 0)] =
        iR ∘ ![t 1, t 0] := by
      funext k
      fin_cases k <;> rfl
    rw [hRevTuple]
    exact hImage

/-- The full finite strong-amalgamation property of the concrete
paired-equivalence class. Both induced side embeddings preserve AND
reflect E, M and the distinguished named linear order. -/
theorem finitePairedClass_strong_amalgamation :
    HasFiniteStrongAmalgamation finitePairedClass := by
  intro D E F hD hE hF Root Left Right hRoot hLeft hRight sL sR
  classical
  letI : Fintype D := Fintype.ofFinite D
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype F := Fintype.ofFinite F
  let P := FreeAmalgam.Vertex Root Left Right sL sR
  let C := FreeAmalgam.amalgam Root Left Right sL sR
  let iL := FreeAmalgam.leftEmbedding Root Left Right sL sR
  let iR := FreeAmalgam.rightEmbedding Root Left Right sL sR
  let hFree := FreeAmalgam.isFreeAmalgam Root Left Right sL sR
  have hP : Finite P := inferInstance
  letI : Finite P := hP
  obtain ⟨Enew, hEquiv, hELeft, hERight, hMateE⟩ :=
    exists_equivalence_amalgam_with_matching
      Root Left Right hRoot.2 hLeft.2 hRight.2 sL sR
  let keyL : E → ℕ ×ₗ (ℕ ×ₗ ℕ) := sideOrderKey Left sL 0
  let keyR : F → ℕ ×ₗ (ℕ ×ₗ ℕ) := sideOrderKey Right sR 1
  have hCompat : ∀ d, keyL (sL d) = keyR (sR d) :=
    sideOrderKey_root_agree sL sR
  have hOrdKeyL : ∀ a b : E, edge Left .lt a b →
      keyL a < keyL b := by
    intro a b hab
    exact sideOrderKey_strictMono Left hLeft.2 sL 0
      (by omega) hab
  have hOrdKeyR : ∀ a b : F, edge Right .lt a b →
      keyR a < keyR b := by
    intro a b hab
    exact sideOrderKey_strictMono Right hRight.2 sR 1
      (by omega) hab
  obtain ⟨o, hOrdL, hOrdR⟩ :=
    hFree.exists_order_from_compatible_keys
      keyL keyR hCompat hOrdKeyL hOrdKeyR
  let Target : RelStructure Lang P where
    rel
      | .lt, t => @LT.lt P o.toLT (t 0) (t 1)
      | .equiv, t => Enew (t 0) (t 1)
      | .mate, t => C.rel .mate t
  have hTarget : pairedClass Target := by
    refine {
      lt_irrefl := ?_
      lt_trans := ?_
      lt_total := ?_
      equiv := hEquiv
      mate_irrefl := ?_
      mate_symm := ?_
      mate_total := ?_
      mate_equiv := ?_
    }
    · intro x hxx
      exact (lt_irrefl x hxx).elim
    · intro x y z hxy hyz
      exact lt_trans hxy hyz
    · intro x y hxy
      exact lt_or_gt_of_ne hxy
    · exact freeAmalgam_mate_irrefl Root Left Right
        hLeft.2 hRight.2 sL sR
    · exact freeAmalgam_mate_symm Root Left Right
        hLeft.2 hRight.2 sL sR
    · exact freeAmalgam_mate_total Root Left Right
        hRoot.2 hLeft.2 hRight.2 sL sR
    · exact hMateE
  let jL : Embedding Left Target := {
    toFun := iL
    injective := iL.injective
    map_rel_iff := by
      intro Rel t
      cases Rel with
      | lt =>
        change (@LT.lt P o.toLT (iL (t 0)) (iL (t 1))) ↔
          edge Left .lt (t 0) (t 1)
        exact order_reflect_of_strict_mono hLeft.2 o iL hOrdL (t 0) (t 1)
      | equiv =>
        change Enew (iL (t 0)) (iL (t 1)) ↔
          edge Left .equiv (t 0) (t 1)
        exact hELeft (t 0) (t 1)
      | mate =>
        change C.rel .mate (iL ∘ t) ↔ Left.rel .mate t
        exact iL.map_rel_iff .mate t
  }
  let jR : Embedding Right Target := {
    toFun := iR
    injective := iR.injective
    map_rel_iff := by
      intro Rel t
      cases Rel with
      | lt =>
        change (@LT.lt P o.toLT (iR (t 0)) (iR (t 1))) ↔
          edge Right .lt (t 0) (t 1)
        exact order_reflect_of_strict_mono hRight.2 o iR hOrdR (t 0) (t 1)
      | equiv =>
        change Enew (iR (t 0)) (iR (t 1)) ↔
          edge Right .equiv (t 0) (t 1)
        exact hERight (t 0) (t 1)
      | mate =>
        change C.rel .mate (iR ∘ t) ↔ Right.rel .mate t
        exact iR.map_rel_iff .mate t
  }
  refine ⟨P, hP, Target, ⟨hP, hTarget⟩, jL, jR, ?_, ?_⟩
  · exact FreeAmalgam.left_right_overlap Root Left Right sL sR
  · intro a b hab
    exact (hFree.overlap a b).mp hab

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
