import AllThoseRamseyClasses.Lifts.EHNPrintedTupleImageClosure
import AllThoseRamseyClasses.Lifts.ForbiddenWeakWitnessMinimization
import Mathlib.Data.Fintype.Card

/-!
# Track D: source-support minimization under the paper-shaped image clause

The manuscript's image-closure condition says that a tuple-surjective
homomorphism-embedding image CONTAINS a full forbidden member.
This need not make the whole induced image forbidden.

This module works with the accurately weaker
HasTupleSurjectiveForbiddenImageClosure contract. If the *actual*
range of a particular forbidden EHN witness is function-closed AND
its map to that actual induced range is tuple-surjective, we obtain
a genuinely INJECTIVE forbidden witness with NO MORE source vertices
mapping into any specified A-only region.

Proof: take the forbidden full substructure P of the induced range;
the full embedding P -> range(f) is injective. Choose one original
source preimage for each vertex in P. These choices are injective,
because the induced-range embedding is injective, and preserve the
side-support predicate. Hence the support-cardinality inequality.

This substantially improves the first image-replacement lemma:
it uses the paper-shaped 'contains forbidden' conclusion instead
of requiring the whole image to lie in F. The hTuple condition is
STILL explicit, and is NOT implied by source input-tuple coverage.

The uniform minimal-witness theorem below assumes hClosed and
hTuple for every potential forbidden witness in the fixed target.
It does NOT establish those hypotheses, any global support descent,
or the unrestricted Section 3 strong amalgamation theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under the actual paper-shaped tuple-image closure, the
forbidden full substructure P of the target-induced range has no
more source vertices in an arbitrary target region than the
ORIGINAL forbidden witness. The source preimage selectors are
injective; unlike a raw weak-image quotient, the target inclusion
used here is genuinely full. -/
theorem forbiddenEHNWitness_injectiveReplacement_of_printedTupleRange
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (w : ForbiddenEHNWitness F Target)
    (hClosed : Target.IsClosed (Set.range w.toTarget))
    (hTuple : OriginalPartialTupleSurjective
      w.source (Target.induce (Set.range w.toTarget) hClosed)
      (fun x => (⟨w.toTarget x, ⟨x, rfl⟩⟩ :
        Set.range w.toTarget))) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
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
  let supportMap :
      {z : Z // v.toTarget z ∈ AOnly} →
        {x : w.Carrier // w.toTarget x ∈ AOnly} :=
    fun z => ⟨choosePreimage z.1, by
      rw [support_eq]
      exact z.2⟩
  have hSupportInjective : Function.Injective supportMap := by
    intro z z' heq
    apply Subtype.ext
    apply choosePreimage_injective
    exact congrArg Subtype.val heq
  have hSupportCount :
      Nat.card {z : Z // v.toTarget z ∈ AOnly} ≤
        Nat.card {x : w.Carrier // w.toTarget x ∈ AOnly} := by
    letI : Fintype {z : Z // v.toTarget z ∈ AOnly} :=
      Fintype.ofFinite _
    letI : Fintype {x : w.Carrier // w.toTarget x ∈ AOnly} :=
      Fintype.ofFinite _
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_injective supportMap hSupportInjective)
  exact ⟨v, hvInjective, hSupportCount⟩

/-- One of the actual GLOBAL left-support minimizers is injective
under the paper-shaped image contract, PROVIDED every forbidden
witness into this fixed target has a closed and tuple-surjective
actual range. This leaves the exact new source-range premise visible
and does not silently identify it with the original closure axiom. -/
theorem exists_injectiveMinimalForbiddenEHNWitness_of_printedTupleRanges
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (hActualRanges :
      ∀ w : ForbiddenEHNWitness F Target,
        ∃ hClosed : Target.IsClosed (Set.range w.toTarget),
          OriginalPartialTupleSurjective
            w.source (Target.induce (Set.range w.toTarget) hClosed)
            (fun x => (⟨w.toTarget x, ⟨x, rfl⟩⟩ :
              Set.range w.toTarget)))
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      ∀ w : ForbiddenEHNWitness F Target,
        v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  obtain ⟨w, hMin⟩ :=
    exists_minimalForbiddenEHNWitness_support
      F Target AOnly hExists
  obtain ⟨hClosed, hTuple⟩ := hActualRanges w
  obtain ⟨v, hInjective, hBound⟩ :=
    forbiddenEHNWitness_injectiveReplacement_of_printedTupleRange
      F hFiniteF hImage Target AOnly w hClosed hTuple
  refine ⟨v, hInjective, ?_⟩
  intro w'
  exact hBound.trans (hMin w')

end AllThoseRamseyClasses.Lifts
