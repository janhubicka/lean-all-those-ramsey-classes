import AllThoseRamseyClasses.Lifts.EHNWeakImageForbiddenLocalTransport
import Mathlib.Data.Fintype.Card

/-!
# Track D: the weakest useful source-generated image-transport interface

The earlier support-preserving replacement lemma assumes that
EVERY full forbidden substructure of the source-generated
tuple-surjective weak quotient Q can be mapped EHN into Target.

For the actual replacement step it suffices to find ONE FULL
forbidden copy P ↪ Q whose inclusion-composite P → Target is EHN.
No claim is made about the other forbidden copies of Q.

Since Source → Q is surjective on vertices, choose a source
preimage of every vertex of P. Those selections are injective
because P ↪ Q is a full embedding. Thus the new forbidden source
P has an injective EHN map into Target with source-side support
bounded by the ORIGINAL witness, for ANY target region AOnly.

This is a strictly weaker sufficient premise than universal
forbidden-copy transport. It is not a consequence of the printed
image-closure axiom in arbitrary targets (the C5/T counterexample
will be an independent negative instance). It remains to establish
this existential source-generated transport in the actual
maximal-lift full free-amalgamation setting, or to replace the
image-quotient step by a collision-tolerant geometric flip.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- There exists at least ONE full forbidden member of the
genuinely tuple-surjective source-generated weak image whose
underlying inclusion into Target is an actual EHN map.

The full quotient need not embed into Target; and none of the
other forbidden copies need be transportable. -/
def HasTransportableForbiddenWeakImageCopy
    (F : ∀ {X : Type}, Structure L X → Prop)
    {UT : Type} (Target : Structure L UT)
    (w : ForbiddenEHNWitness F Target) : Prop :=
  ∃ (Z : Type) (P : Structure L Z),
    F P ∧
    ∃ e : Structure.Embedding P
      (Structure.weakImage w.source Target w.toTarget),
      P.IsEHNHomomorphismEmbedding Target (fun z => (e z).1)

/-- A transportable forbidden weak-image copy gives an ACTUAL
injective replacement with no increase in source-vertex support.
The proof requires neither the family image-closure axiom nor
tuple coverage on the full target-induced image: those are
separate ways to obtain the existential copy, not assumptions
of this selection/cardinality argument. -/
theorem forbiddenWeakImage_injectiveReplacement_of_existsTransportableCopy
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (w : ForbiddenEHNWitness F Target)
    (hExists : HasTransportableForbiddenWeakImageCopy F Target w) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  classical
  letI : Finite w.Carrier := w.finiteCarrier
  obtain ⟨Z, P, hP, e, hTransport⟩ := hExists
  letI : Finite Z := hFiniteF P hP
  let q : w.Carrier → Set.range w.toTarget :=
    Structure.weakImage.quotientMap (f := w.toTarget)
  have hSurj : Function.Surjective q :=
    Structure.weakImage.quotientMap_surjective (f := w.toTarget)
  let g : Z → UT := fun z => (e z).1
  have hgInjective : Function.Injective g := by
    intro z z' heq
    exact e.injective (Subtype.ext heq)
  let v : ForbiddenEHNWitness F Target := {
    Carrier := Z
    finiteCarrier := inferInstance
    source := P
    forbidden := hP
    toTarget := g
    homEmbedding := hTransport
  }
  let pickPreimage (z : Z) : w.Carrier :=
    Classical.choose (hSurj (e z))
  have hPick (z : Z) : q (pickPreimage z) = e z :=
    Classical.choose_spec (hSurj (e z))
  have hPickInjective : Function.Injective pickPreimage := by
    intro z z' heq
    apply e.injective
    calc
      e z = q (pickPreimage z) := (hPick z).symm
      _ = q (pickPreimage z') := congrArg q heq
      _ = e z' := hPick z'
  have hTargetEq (z : Z) :
      w.toTarget (pickPreimage z) = v.toTarget z := by
    change (q (pickPreimage z)).1 = (e z).1
    exact congrArg Subtype.val (hPick z)
  let supportMap :
      {z : Z // v.toTarget z ∈ AOnly} →
      {x : w.Carrier // w.toTarget x ∈ AOnly} :=
    fun z => ⟨pickPreimage z.1, by
      rw [hTargetEq]
      exact z.2⟩
  have hSupportInj : Function.Injective supportMap := by
    intro z z' h
    apply Subtype.ext
    exact hPickInjective (congrArg Subtype.val h)
  have hBound :
      Nat.card {z : Z // v.toTarget z ∈ AOnly} ≤
      Nat.card {x : w.Carrier // w.toTarget x ∈ AOnly} := by
    letI : Fintype {z : Z // v.toTarget z ∈ AOnly} :=
      Fintype.ofFinite _
    letI : Fintype {x : w.Carrier // w.toTarget x ∈ AOnly} :=
      Fintype.ofFinite _
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_injective supportMap hSupportInj)
  exact ⟨v, hgInjective, hBound⟩

/-- One transportable forbidden weak-image copy per actual
forbidden witness is enough to guarantee an injective GLOBAL
minimum of original A-only source-support counts. The condition
is existential over copies of each generated image, not universal. -/
theorem exists_injectiveMinimalForbiddenEHNWitness_of_existsTransportableCopy
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (hCopy : ∀ w : ForbiddenEHNWitness F Target,
      HasTransportableForbiddenWeakImageCopy F Target w)
    (hNonempty : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      ∀ w : ForbiddenEHNWitness F Target,
        v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  obtain ⟨w, hMin⟩ :=
    exists_minimalForbiddenEHNWitness_support
      F Target AOnly hNonempty
  obtain ⟨v, hvInj, hBound⟩ :=
    forbiddenWeakImage_injectiveReplacement_of_existsTransportableCopy
      F hFiniteF Target AOnly w (hCopy w)
  refine ⟨v, hvInj, ?_⟩
  intro w'
  exact hBound.trans (hMin w')

/-- The older full-forbidden-image universal transport hypothesis,
together with the PRINTED family image-closure axiom, implies
the new weaker existential interface. Crucially the quotient
itself is original-partial HE and tuple-surjective regardless of
extra relations in the ambient target's full induced range. -/
theorem hasTransportableForbiddenWeakImageCopy_of_printedClosure_and_allTransport
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {UT : Type} (Target : Structure L UT)
    (w : ForbiddenEHNWitness F Target)
    (hTransport : ForbiddenFullWeakImagePiecesTransport F Target w) :
    HasTransportableForbiddenWeakImageCopy F Target w := by
  let Q : Structure L (Set.range w.toTarget) :=
    Structure.weakImage w.source Target w.toTarget
  let q : w.Carrier → Set.range w.toTarget :=
    Structure.weakImage.quotientMap (f := w.toTarget)
  obtain ⟨_, hqHE, hqTuple⟩ :=
    originalPartialHE_weakImage_quotient_data
      w.source Target w.toTarget
      w.homEmbedding.toOriginalPartial
  obtain ⟨Z, P, hP, ⟨e⟩⟩ :=
    hImage w.source Q q w.forbidden hqHE hqTuple
  exact ⟨Z, P, hP, e, hTransport P hP e⟩

end AllThoseRamseyClasses.Lifts
