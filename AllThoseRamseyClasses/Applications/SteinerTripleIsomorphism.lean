import AllThoseRamseyClasses.Applications.SteinerTripleHereditary
import AllThoseRamseyClasses.Published.InducedClosed2019HereditaryBridge

/-!
# Isomorphism invariance of the ordered Steiner triple class

Ordinary closed heredity is NOT enough to establish invariance under
a surjective full embedding without first transporting U-closedness
backwards.  We construct the genuine full inverse and apply the
previously verified surjective closedness transport theorem.

This discharges the explicit isomorphism-closedness field of the
coordinated corrected 2019 class API. It does not discharge strong
amalgamation or exact local completion.
-/

namespace AllThoseRamseyClasses.Applications.SteinerTriples

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published

theorem orderedSteiner_isomorphismClosed :
    IsomorphismClosed2019 orderedSteinerClass := by
  intro X Y A B e hSurj hB
  classical
  have hPreimage :
      ∀ y : Y, ∃ x : X, (Embedding.id B) y = e x := by
    intro y
    obtain ⟨x, hx⟩ := hSurj y
    exact ⟨x, hx.symm⟩
  let eInv : Embedding B A :=
    (Embedding.id B).factorThroughRange e hPreimage
  have hInvRight (y : Y) : e (eInv y) = y := by
    change e (Classical.choose (hPreimage y)) = y
    exact (Classical.choose_spec (hPreimage y)).symm
  have hInvSurj : Function.Surjective eInv := by
    intro x
    refine ⟨e x, ?_⟩
    apply e.injective
    exact hInvRight (e x)
  have hAClosed : IsUClosed blockRules A :=
    isUClosed_of_surjective_embedding eInv hInvSurj
      (orderedSteiner_isUClosed B hB)
  exact orderedSteiner_of_closed_embedding A B hB hAClosed e

end AllThoseRamseyClasses.Applications.SteinerTriples
