import AllThoseRamseyClasses.Lifts.EHNPrintedTupleSupportMinimizer

/-!
# Simultaneous support bounds for the SAME printed-tuple image witness

The original 2019 (weak) image-closure contract states that
a tuple-surjective homomorphism-embedding image CONTAINS some full
forbidden member; it does not say the entire induced image is
forbidden. The checked source-specific replacement lemma only
recorded support nonincrease for ONE preselected target region.

Here the single forbidden member P and the single full embedding
P -> Target.induce(range f) are chosen ONCE. A single injective
original-source preimage selector is fixed on the entire carrier
of P, and therefore works simultaneously for EVERY target region.

This lets (A,B)-lex-minimality survive the SAME injectivization,
without assuming the stronger vertex-surjective EHN-closed family.
The actual image MUST be function-closed and the map into its
full induced native range MUST be original-partial tuple-surjective.
These are independent obligations in a functional language.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- One original F-forbidden weak EHN source/map whose actual range
is FUNCTION-CLOSED and whose induced-range map is genuinely OLD
tuple-surjective admits ONE injective full original F-forbidden
replacement with support count bounded in EVERY target set at once.

The family assumption is precisely the printed tuple-surjective
'contains a full forbidden member' clause, NOT closure of the entire
image under vertex-surjective EHN maps. No target-image collision
is assumed absent in the input. -/
theorem forbiddenEHNWitness_injectiveReplacement_allSupport_of_printedTupleRange
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {UT : Type} (Target : Structure L UT)
    (w : ForbiddenEHNWitness F Target)
    (hClosed : Target.IsClosed (Set.range w.toTarget))
    (hTuple : OriginalPartialTupleSurjective
      w.source (Target.induce (Set.range w.toTarget) hClosed)
      (fun x => (⟨w.toTarget x, ⟨x, rfl⟩⟩ :
        Set.range w.toTarget))) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      ∀ Active : Set UT,
        v.sourceSupportCount Active ≤ w.sourceSupportCount Active := by
  classical
  letI : Finite w.Carrier := w.finiteCarrier
  let S : Set UT := Set.range w.toTarget
  let Q : Structure L S := Target.induce S hClosed
  let q : w.Carrier → S := fun x => ⟨w.toTarget x, ⟨x, rfl⟩⟩
  have hqData :=
    ehn_closedRange_surjectiveInducedFactor
      w.source Target w.toTarget w.homEmbedding hClosed
  obtain ⟨Z, P, hP, ⟨e⟩⟩ :=
    hImage w.source Q q w.forbidden hqData.1.toOriginalPartial hTuple
  letI : Finite Z := hFiniteF P hP
  let emb : Structure.Embedding P Target :=
    (Target.inclusion S hClosed).comp e
  let v : ForbiddenEHNWitness F Target := {
    Carrier := Z
    finiteCarrier := inferInstance
    source := P
    forbidden := hP
    toTarget := emb
    homEmbedding := emb.isEHNHomomorphismEmbedding
  }
  have hvInjective : Function.Injective v.toTarget := emb.injective
  let choosePreimage (z : Z) : w.Carrier :=
    Classical.choose (hqData.2 (e z))
  have choosePreimage_spec (z : Z) :
      q (choosePreimage z) = e z :=
    Classical.choose_spec (hqData.2 (e z))
  have choosePreimage_injective :
      Function.Injective choosePreimage := by
    intro z z' heq
    apply e.injective
    calc
      e z = q (choosePreimage z) := (choosePreimage_spec z).symm
      _ = q (choosePreimage z') := congrArg q heq
      _ = e z' := choosePreimage_spec z'
  have support_eq (z : Z) :
      w.toTarget (choosePreimage z) = v.toTarget z := by
    change (q (choosePreimage z)).1 = (e z).1
    exact congrArg Subtype.val (choosePreimage_spec z)
  refine ⟨v, hvInjective, ?_⟩
  intro Active
  let supportMap :
      {z : Z // v.toTarget z ∈ Active} →
        {x : w.Carrier // w.toTarget x ∈ Active} :=
    fun z => ⟨choosePreimage z.1, by
      rw [support_eq]
      exact z.2⟩
  have hSupportInjective : Function.Injective supportMap := by
    intro z z' heq
    apply Subtype.ext
    apply choosePreimage_injective
    exact congrArg Subtype.val heq
  change Nat.card {z : Z // v.toTarget z ∈ Active} ≤
    Nat.card {x : w.Carrier // w.toTarget x ∈ Active}
  letI : Fintype {z : Z // v.toTarget z ∈ Active} :=
    Fintype.ofFinite _
  letI : Fintype {x : w.Carrier // w.toTarget x ∈ Active} :=
    Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_le_of_injective supportMap hSupportInjective)

end AllThoseRamseyClasses.Lifts
