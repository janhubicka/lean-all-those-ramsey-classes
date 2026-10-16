import PartiteConstruction.Functional.WeakAttachment

/-!
# Compatible weak maps fold over ANY actual functional free amalgam

The 2019 lift flip often begins with a forbidden source that has a
geometrically established free-amalgam decomposition, rather than
with the library's canonical free-amalgam carrier.

The reusable map fold below works for ANY full free-amalgam
certificate. It is defined by choosing an old-side preimage if
available, otherwise a right-side preimage. The overlap condition
makes the two side maps compatible wherever both apply.

It follows from the checked weak-EHN amalgam theorem that the fold
is a weak functional homomorphism-embedding, with positive function
incidences preserved and full embeddings on all functionally
irreducible source copies. No equality of whole function fibres
is imposed on the maps; global injectivity is not assumed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F C Z : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C} {Target : Structure L Z}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- Fold compatible vertex maps across an arbitrary concrete
FULL functional free-amalgam diagram. -/
noncomputable def compatibleFunctionalFold
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (pL : E → Z) (pR : F → Z)
    (hcompat : ∀ r, pL (sL r) = pR (sR r)) : C → Z := by
  classical
  intro z
  exact if h : ∃ a : E, z = iL a then
      pL (Classical.choose h)
    else
      pR (Classical.choose ((hfree.covers z).resolve_left h))

/-- The compatible fold restricts EXACTLY to the left map. -/
theorem compatibleFunctionalFold_left
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (pL : E → Z) (pR : F → Z)
    (hcompat : ∀ r, pL (sL r) = pR (sR r))
    (a : E) :
    compatibleFunctionalFold hfree pL pR hcompat (iL a) = pL a := by
  classical
  unfold compatibleFunctionalFold
  have h : ∃ b : E, iL a = iL b := ⟨a, rfl⟩
  rw [dif_pos h]
  have heq : a = Classical.choose h :=
    iL.injective (Classical.choose_spec h)
  exact congrArg pL heq.symm

/-- The compatible fold restricts EXACTLY to the right map,
including root vertices which lie on both sides. -/
theorem compatibleFunctionalFold_right
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (pL : E → Z) (pR : F → Z)
    (hcompat : ∀ r, pL (sL r) = pR (sR r))
    (b : F) :
    compatibleFunctionalFold hfree pL pR hcompat (iR b) = pR b := by
  classical
  by_cases h : ∃ a : E, iR b = iL a
  · unfold compatibleFunctionalFold
    rw [dif_pos h]
    have hroot : iL (Classical.choose h) = iR b :=
      (Classical.choose_spec h).symm
    obtain ⟨r, hrL, hrR⟩ :=
      (hfree.overlap (Classical.choose h) b).mp hroot
    calc
      pL (Classical.choose h) = pL (sL r) :=
        congrArg pL hrL
      _ = pR (sR r) := hcompat r
      _ = pR b := congrArg pR hrR.symm
  · unfold compatibleFunctionalFold
    rw [dif_neg h]
    let hb : ∃ c : F, iR b = iR c :=
      (hfree.covers (iR b)).resolve_left h
    change pR (Classical.choose hb) = pR b
    have heq : Classical.choose hb = b :=
      iR.injective (Classical.choose_spec hb).symm
    exact congrArg pR heq

/-- The compatible fold is a genuine 2019-style WEAK functional
homomorphism-embedding to the target. This includes full
reflection on every embedded functional irreducible. -/
theorem compatibleFunctionalFold_isEHNHomomorphismEmbedding
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (pL : E → Z) (pR : F → Z)
    (hcompat : ∀ r, pL (sL r) = pR (sR r))
    (hpL : Left.IsEHNHomomorphismEmbedding Target pL)
    (hpR : Right.IsEHNHomomorphismEmbedding Target pR) :
    Whole.IsEHNHomomorphismEmbedding Target
      (compatibleFunctionalFold hfree pL pR hcompat) := by
  exact Structure.IsEHNHomomorphismEmbedding.of_freeAmalgam
    hfree hpL hpR
    (fun a => compatibleFunctionalFold_left hfree pL pR hcompat a)
    (fun b => compatibleFunctionalFold_right hfree pL pR hcompat b)

end AllThoseRamseyClasses.Lifts
