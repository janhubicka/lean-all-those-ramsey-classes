import AllThoseRamseyClasses.Published.CoordinatedCycleClosedCliques
import AllThoseRamseyClasses.Published.CoordinatedWeakPairedCompletionTarget
import AllThoseRamseyClasses.Published.OrderedAmbient
import PartiteConstruction.Ramsey.ClosureClosedCompletionRank

/-!
# Reduce exact weak (4c) to one concrete pairwise reflection condition

For each exact weak S, the finite structure D(k,S) already belongs
to K, with a complete E equivalence relation, total order and
perfect matching. Its carrier is the ENTIRE original CycleVertex k.

To prove the actual weak induced Ck|S has a protected K-completion
via the canonical inclusion into D(k,S), it suffices to show that
D(k,S) reflects the three relations on those pairs x,y in S whose
matching blocks lie in one common gadget.

The positive homomorphism is automatic since every original
tuple has gadget-related endpoints. For protected closed
U-irreducible tests, the already Green closed-cover theorem shows
all their matching blocks are pairwise gadget-related. Thus the
same local reflection hypothesis supplies a genuine full embedding
on the original test carrier, with NO closure of S and no change
of the tested n-vertex bound.

The remaining obligation is a finite case split on the 3x3 blocks
of each installed gadget, especially the cross-block E tuples.
This module never hides that hypothesis in an axiom or instance.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The ONLY remaining relation-reflection property needed
to turn explicit D(k,S) into a K-completion of exact weak Ck|S. -/
def CycleWeakRelatedAgreement (k : ℕ)
    (S : Finset (CycleVertex k)) : Prop :=
  ∀ (R : Symbol) (x y : CycleVertex k),
    x ∈ S → y ∈ S →
    cycleRelatedBlocks k x.1 y.1 →
    (edge (cycleWeakCandidate k S) R x y ↔
      edge (cycleGadgetWitness k) R x y)

/-- The canonical map of EXACT weak source vertices into the full
K-member is a positive homomorphism whenever related pairs reflect. -/
theorem cycleWeak_id_homomorphism_of_related
    (k : ℕ) (S : Finset (CycleVertex k))
    (hAgree : CycleWeakRelatedAgreement k S) :
    ((cycleGadgetWitness k).induce (↑S : Set (CycleVertex k))).IsHomomorphism
      (cycleWeakCandidate k S) Subtype.val := by
  intro R t ht
  have htup : (Subtype.val ∘ t) =
      ![(t 0).1,(t 1).1] := by
    funext i
    fin_cases i <;> rfl
  have hC : edge (cycleGadgetWitness k) R (t 0).1 (t 1).1 := by
    change (cycleGadgetWitness k).rel R (Subtype.val ∘ t) at ht
    rw [htup] at ht
    exact ht
  have hRelated : cycleRelatedBlocks k (t 0).1.1 (t 1).1.1 :=
    cycleGadgetWitness_edge_supported k R (t 0).1 (t 1).1 hC
  have hD := (hAgree R (t 0).1 (t 1).1
    (t 0).2 (t 1).2 hRelated).mpr hC
  change (cycleWeakCandidate k S).rel R (Subtype.val ∘ t)
  rw [htup]
  exact hD

/-- Every closed test into the EXACT weak induced source embeds
into the new finite K-target, without adjoining missing matching
partners to the TEST and without requiring S to be closed. -/
theorem cycleWeak_closedTest_embedding_of_related
    (k : ℕ) (S : Finset (CycleVertex k))
    (hAgree : CycleWeakRelatedAgreement k S)
    {X : Type} (Test : RelStructure Lang X)
    (hClosed : IsUClosed mateRules Test)
    (hIrred : IsUIrreducible mateRules Test)
    (e : Embedding Test
      ((cycleGadgetWitness k).induce (↑S : Set (CycleVertex k)))) :
    ∃ j : Embedding Test (cycleWeakCandidate k S),
      ∀ x, j x = (e x).1 := by
  let eWhole : Embedding Test (cycleGadgetWitness k) :=
    (inclusion (cycleGadgetWitness k)
      (↑S : Set (CycleVertex k))).comp e
  have hRelated (a b : X) :
      cycleRelatedBlocks k (e a).1.1 (e b).1.1 :=
    cycle_closedUIrreducible_blocks_pairwise_related
      k Test hClosed hIrred eWhole a b
  let j : Embedding Test (cycleWeakCandidate k S) := {
    toFun := fun x => (e x).1
    injective := by
      intro a b hab
      apply e.injective
      exact Subtype.ext hab
    map_rel_iff := by
      intro R t
      have hTuple : t = ![t 0,t 1] := by
        funext i
        fin_cases i <;> rfl
      have hSourceTuple : (e ∘ t) = ![e (t 0),e (t 1)] := by
        funext i
        fin_cases i <;> rfl
      have hTargetTuple : ((fun x => (e x).1) ∘ t) =
          ![(e (t 0)).1,(e (t 1)).1] := by
        funext i
        fin_cases i <;> rfl
      have hC : edge (cycleGadgetWitness k) R
          (e (t 0)).1 (e (t 1)).1 ↔ Test.rel R t := by
        have he := e.map_rel_iff R t
        have hInduceTuple : (Subtype.val ∘ (e ∘ t)) =
            ![(e (t 0)).1,(e (t 1)).1] := by
          funext q
          fin_cases q <;> rfl
        change (cycleGadgetWitness k).rel R
            (Subtype.val ∘ (e ∘ t)) ↔ Test.rel R t at he
        rw [hInduceTuple] at he
        exact he
      have hD : edge (cycleWeakCandidate k S) R
          (e (t 0)).1 (e (t 1)).1 ↔
          edge (cycleGadgetWitness k) R
            (e (t 0)).1 (e (t 1)).1 :=
        hAgree R (e (t 0)).1 (e (t 1)).1
          (e (t 0)).2 (e (t 1)).2 (hRelated (t 0) (t 1))
      change (cycleWeakCandidate k S).rel R
          ((fun x => (e x).1) ∘ t) ↔ Test.rel R t
      rw [hTargetTuple]
      exact hD.trans hC
  }
  exact ⟨j,fun _ => rfl⟩

/-- Discharge the ACTUAL exact weak n-vertex K-completion obligation
from related-pair agreement; its finite K target is explicit D(k,S),
and no source test is enlarged to its closure. -/
theorem cycleWeak_hasClosedUKCompletion_of_related
    (k : ℕ) (S : Finset (CycleVertex k))
    (hAgree : CycleWeakRelatedAgreement k S) :
    HasClosedUKCompletion finitePairedClass mateRules
      ((cycleGadgetWitness k).induce (↑S : Set (CycleVertex k))) := by
  let D := cycleWeakCandidate k S
  have hD : finitePairedClass D := cycleWeakCandidate_mem_K k S
  have hIrred : D.Irreducible :=
    orderedAmbient_irreducible D
      (finitePairedClass_subset_orderedAmbient D hD)
  refine ⟨CycleVertex k, inferInstance, D, hD, hIrred,
    Subtype.val, ?_⟩
  refine ⟨cycleWeak_id_homomorphism_of_related k S hAgree, ?_⟩
  intro X Test hClosed hIrredTest e
  exact cycleWeak_closedTest_embedding_of_related
    k S hAgree Test hClosed hIrredTest e

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
