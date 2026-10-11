import AllThoseRamseyClasses.Published.CoordinatedCycleGadgetReflection
import AllThoseRamseyClasses.Published.CoordinatedControlEGadgetProfiles
import AllThoseRamseyClasses.Published.CoordinatedWeakClosingEPrivate
import AllThoseRamseyClasses.Published.CoordinatedWeakOrderReflection
import AllThoseRamseyClasses.Published.CoordinatedWeakEGadgetTags

/-!
# Every exact weak <=k-vertex test reflects E on all installed gadgets

The finite K completion D(k,S) uses missing-block component labels.
On one path gadget, the two backbone blocks have a common E-class
whenever both occur in the exact weak source S, and the private D
block is E-disjoint from them. On the closing gadget, b0~T while
b0 and the final backbone block are inequivalent, and T is also
inequivalent to the final block, by the missing internal gap.

This formalizes all NINE ordered pairs of the three matching blocks
in each kind of installed gadget. Each block has two matched vertices
and relation E is independent of the bit. The source E definition
is pulled back from the 10-vertex C0 control on gadget-supported pairs.

This file does NOT yet assert HasClosedUKCompletion or the full
locally finite axiom: this E reflection will combine with the
already verified order and M reflection, and then the general
closed-test factorization from PR #86.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- E in the finite K target is symmetric because it is equality
of explicit finite component tags. -/
private theorem weakCandidate_E_symm
    (k : ℕ) (S : Finset (CycleVertex k))
    {x y : CycleVertex k}
    (h : edge (cycleWeakCandidate k S) .equiv x y) :
    edge (cycleWeakCandidate k S) .equiv y x := by
  change cycleWeakEClass k S x = cycleWeakEClass k S y at h
  change cycleWeakEClass k S y = cycleWeakEClass k S x
  exact h.symm

private theorem iff_of_two_true {P Q : Prop} (hP : P) (hQ : Q) :
    P ↔ Q := ⟨fun _ => hQ, fun _ => hP⟩

private theorem iff_of_two_false {P Q : Prop} (hP : ¬ P) (hQ : ¬ Q) :
    P ↔ Q :=
  ⟨fun p => False.elim (hP p), fun q => False.elim (hQ q)⟩

/-- Every ordered pair of vertices of ONE installed gadget has
precisely the same E relation in Ck and its explicit K completion,
provided the two vertices are in the exact weak S (|S|≤k). -/
theorem cycleWeakCandidate_E_iff_of_common_gadget (k : ℕ)
    (S : Finset (CycleVertex k)) (hCard : S.card ≤ k)
    (g : CycleGadget k) (x y : CycleVertex k)
    (hxg : cycleGadgetContains k g x.1)
    (hyg : cycleGadgetContains k g y.1)
    (hxs : x ∈ S) (hys : y ∈ S) :
    edge (cycleWeakCandidate k S) .equiv x y ↔
      edge (cycleGadgetWitness k) .equiv x y := by
  have hControl : edge (cycleGadgetWitness k) .equiv x y ↔
      cycleControlELabels
        (cycleBlockLabel k x.1) (cycleBlockLabel k y.1) :=
    (cycleGadgetWitness_E_iff_control_of_common_gadget
      k g x y hxg hyg).trans
      (cycleControlVertex_E_iff_labels k x y)
  suffices hTarget : edge (cycleWeakCandidate k S) .equiv x y ↔
      cycleControlELabels
        (cycleBlockLabel k x.1) (cycleBlockLabel k y.1) by
    exact hTarget.trans hControl.symm
  rcases x with ⟨a,u⟩
  rcases y with ⟨b,v⟩
  have sameBlock (b : CycleBlock k) (u v : Fin 2) :
      edge (cycleWeakCandidate k S) .equiv (b,u) (b,v) := by
    change cycleWeakEClass k S (b,u) = cycleWeakEClass k S (b,v)
    rfl
  have controlSame (b : CycleBlock k) :
      cycleControlELabels (cycleBlockLabel k b)
        (cycleBlockLabel k b) := Or.inl rfl
  cases g with
  | inl i =>
      rcases cyclePath_gadget_block_cases k i a hxg with ha | ha | ha <;>
        rcases cyclePath_gadget_block_cases k i b hyg with hb | hb | hb
      · subst a
        subst b
        exact iff_of_two_true (sameBlock (cyclePathStart k i) u v)
          (controlSame (cyclePathStart k i))
      · subst a
        subst b
        exact iff_of_two_true
          (cycleWeakCandidate_path_backbone_E_positive k S i u v
          ⟨u, hxs⟩)
          (cycleControlELabels_pathStartFinish k i)
      · subst a
        subst b
        exact iff_of_two_false
          (cycleWeakCandidate_path_first_private_E_negative k S i u v)
          (cycleControlELabels_pathStartPrivate_neg k i)
      · subst a
        subst b
        exact iff_of_two_true
          (weakCandidate_E_symm k S
          (cycleWeakCandidate_path_backbone_E_positive k S i v u
            ⟨v, hys⟩))
          (cycleControlELabels_symm _ _
          (cycleControlELabels_pathStartFinish k i))
      · subst a
        subst b
        exact iff_of_two_true (sameBlock (cyclePathFinish k i) u v)
          (controlSame (cyclePathFinish k i))
      · subst a
        subst b
        exact iff_of_two_false
          (cycleWeakCandidate_path_second_private_E_negative k S i u v)
          (cycleControlELabels_pathFinishPrivate_neg k i)
      · subst a
        subst b
        exact iff_of_two_false
          (fun he => cycleWeakCandidate_path_first_private_E_negative k S i v u
          (weakCandidate_E_symm k S he))
          (fun he => cycleControlELabels_pathStartPrivate_neg k i
          (cycleControlELabels_symm _ _ he))
      · subst a
        subst b
        exact iff_of_two_false
          (fun he => cycleWeakCandidate_path_second_private_E_negative k S i v u
          (weakCandidate_E_symm k S he))
          (fun he => cycleControlELabels_pathFinishPrivate_neg k i
          (cycleControlELabels_symm _ _ he))
      · subst a
        subst b
        exact iff_of_two_true (sameBlock (cycleEdgePrivateBlock k i) u v)
          (controlSame (cycleEdgePrivateBlock k i))
  | inr _ =>
      rcases cycleClosing_gadget_block_cases k a hxg with ha | ha | ha <;>
        rcases cycleClosing_gadget_block_cases k b hyg with hb | hb | hb
      · subst a
        subst b
        exact iff_of_two_true (sameBlock (cycleClosingFirst k) u v)
          (controlSame (cycleClosingFirst k))
      · subst a
        subst b
        exact iff_of_two_false
          (cycleWeakCandidate_closing_backbone_E_negative k S hCard u v)
          (cycleControlELabels_closingFirstLast_neg k)
      · subst a
        subst b
        exact iff_of_two_true
          (cycleWeakCandidate_closing_first_private_E_positive k S u v)
          (cycleControlELabels_closingFirstPrivate k)
      · subst a
        subst b
        exact iff_of_two_false
          (fun he => cycleWeakCandidate_closing_backbone_E_negative k S hCard v u
          (weakCandidate_E_symm k S he))
          (fun he => cycleControlELabels_closingFirstLast_neg k
          (cycleControlELabels_symm _ _ he))
      · subst a
        subst b
        exact iff_of_two_true (sameBlock (cycleClosingLast k) u v)
          (controlSame (cycleClosingLast k))
      · subst a
        subst b
        exact iff_of_two_false
          (cycleWeakCandidate_closing_last_private_E_negative k S hCard u v)
          (cycleControlELabels_closingLastPrivate_neg k)
      · subst a
        subst b
        exact iff_of_two_true
          (weakCandidate_E_symm k S
          (cycleWeakCandidate_closing_first_private_E_positive k S v u))
          (cycleControlELabels_symm _ _
          (cycleControlELabels_closingFirstPrivate k))
      · subst a
        subst b
        exact iff_of_two_false
          (fun he => cycleWeakCandidate_closing_last_private_E_negative k S hCard v u
          (weakCandidate_E_symm k S he))
          (fun he => cycleControlELabels_closingLastPrivate_neg k
          (cycleControlELabels_symm _ _ he))
      · subst a
        subst b
        exact iff_of_two_true (sameBlock (cycleClosingPrivateBlock k) u v)
          (controlSame (cycleClosingPrivateBlock k))

/-- On every gadget-related pair IN the exact weak test, the
completed equivalence relation agrees with the original partial E. -/
theorem cycleWeakCandidate_E_iff_of_related (k : ℕ)
    (S : Finset (CycleVertex k)) (hCard : S.card ≤ k)
    (x y : CycleVertex k)
    (hx : x ∈ S) (hy : y ∈ S)
    (hRel : cycleRelatedBlocks k x.1 y.1) :
    edge (cycleWeakCandidate k S) .equiv x y ↔
      edge (cycleGadgetWitness k) .equiv x y := by
  rcases hRel with hSame | ⟨g,hgx,hgy⟩
  · have hTarget : edge (cycleWeakCandidate k S) .equiv x y := by
      apply cycleWeakCandidate_E_of_sameBlock k S x y hSame
    have hSource : edge (cycleGadgetWitness k) .equiv x y := by
      change cycleRelatedBlocks k x.1 y.1 ∧
        edge CycleControlC0 .equiv
          (cycleControlVertex k x) (cycleControlVertex k y)
      refine ⟨Or.inl hSame, ?_⟩
      rw [cycleControlVertex_E_iff_labels]
      rw [hSame]
      exact Or.inl rfl
    exact iff_of_two_true hTarget hSource
  · exact cycleWeakCandidate_E_iff_of_common_gadget
      k S hCard g x y hgx hgy hx hy

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
