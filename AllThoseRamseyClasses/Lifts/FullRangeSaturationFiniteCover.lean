import AllThoseRamseyClasses.Lifts.FullRangeEHNSaturation
import AllThoseRamseyClasses.Lifts.GlobalCountableTraceRepresentatives

/-!
# Finite full-isomorphism representatives of bounded saturation

A finite native signature and a uniform bound on original forbidden
source size give a FINITE type of actual saturated representatives.
Every saturated structure is FULLY isomorphic to one of these labelled
representatives. This supplies the bounded finite-family enumeration
step of the repair without assuming that saturation preserves arbitrary
infinite-family regularity. The counting result also allows functions;
function-free hypotheses are needed elsewhere for image normalization.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Actual saturated structures on bounded canonical finite carriers.
This is a concrete finite cover, not an informal quotient by isomorphism. -/
def BoundedSaturatedFinRepresentatives
    (F : ∀ {W : Type}, Structure L W → Prop) (N : ℕ) :=
  Σ n : Fin (N + 1),
    {A : Structure L (Fin n.val) // FullRangeEHNSaturation F A}

/-- Finitely many complete native tables on each of finitely many
carrier sizes. Relations and entire set-valued function fibres count. -/
theorem boundedSaturatedFinRepresentatives_finite
    (F : ∀ {W : Type}, Structure L W → Prop) (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (BoundedSaturatedFinRepresentatives F N) := by
  classical
  letI (n : Fin (N + 1)) : Finite (Structure L (Fin n.val)) :=
    finiteNativeStructures_onFiniteCarrier L (Fin n.val)
  unfold BoundedSaturatedFinRepresentatives
  infer_instance

/-- Every saturated member is represented on a bounded Fin carrier
by a SURJECTIVE FULL embedding. Relabelling preserves saturation
by cancelling that full embedding from the original EHN witness.
No isomorphism-closure premise on the original family is needed. -/
theorem fullRangeEHNSaturation_bounded_fullIsoCover
    (F : ∀ {W : Type}, Structure L W → Prop) (N : ℕ)
    (hBound : ∀ {V : Type} (A : Structure L V), F A → Nat.card V ≤ N)
    {W : Type} (Y : Structure L W)
    (hY : FullRangeEHNSaturation F Y) :
    ∃ p : BoundedSaturatedFinRepresentatives F N,
      ∃ e : Structure.Embedding p.2.1 Y, Function.Surjective e := by
  classical
  letI : Finite W := finite_of_fullRangeEHNSaturation F Y hY
  letI : Fintype W := Fintype.ofFinite W
  have hSize : Fintype.card W ≤ N := by
    simpa only [Nat.card_eq_fintype_card] using
      fullRangeEHNSaturation_card_le F N hBound Y hY
  let n : Fin (N + 1) := ⟨Fintype.card W, Nat.lt_succ_of_le hSize⟩
  let e : Fin n.val ≃ W := (Fintype.equivFin W).symm
  let Z : Structure L (Fin n.val) := functionalStructureRelabel Y e
  let j : Structure.Embedding Z Y := functionalStructureRelabelEmbedding Y e
  have hZ : FullRangeEHNSaturation F Z := by
    obtain ⟨V, Source, hFinite, hF, f, hf, hSurj⟩ := hY
    let q : V → Fin n.val := fun x => e.symm (f x)
    have hq : Source.IsEHNHomomorphismEmbedding Z q := by
      apply ehnHomomorphismEmbedding_cancel_full hf j
      intro x
      exact (e.apply_symm_apply (f x)).symm
    have hqSurj : Function.Surjective q := e.symm.surjective.comp hSurj
    exact ⟨V, Source, hFinite, hF, q, hq, hqSurj⟩
  exact ⟨⟨n, ⟨Z, hZ⟩⟩, j, e.surjective⟩

/-- Finite full-isomorphism cover, including actual representative
coverage for every saturated member on any carrier. -/
theorem fullRangeEHNSaturation_finite_fullIsoCover
    (F : ∀ {W : Type}, Structure L W → Prop) (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hBound : ∀ {V : Type} (A : Structure L V), F A → Nat.card V ≤ N) :
    Finite (BoundedSaturatedFinRepresentatives F N) ∧
      ∀ {W : Type} (Y : Structure L W), FullRangeEHNSaturation F Y →
        ∃ p : BoundedSaturatedFinRepresentatives F N,
          ∃ e : Structure.Embedding p.2.1 Y, Function.Surjective e := by
  refine ⟨boundedSaturatedFinRepresentatives_finite F N, ?_⟩
  intro W Y hY
  exact fullRangeEHNSaturation_bounded_fullIsoCover F N hBound Y hY

end AllThoseRamseyClasses.Lifts
