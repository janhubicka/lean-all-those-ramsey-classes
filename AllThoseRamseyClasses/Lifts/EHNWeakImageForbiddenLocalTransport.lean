import AllThoseRamseyClasses.Lifts.EHNPrintedTupleSupportMinimizer
import AllThoseRamseyClasses.Lifts.OriginalPartialWeakImageQuotient
import Mathlib.Data.Fintype.Card

/-!
# Track D: printed image closure using the genuinely tuple-surjective weak quotient

In the original Section 3 proof, an arbitrary EHN map of a forbidden
source into Target produces a SOURCE-GENERATED weak-image quotient Q.
The map Source -> Q is a genuine original-partial homomorphism-
embedding and is tuple-surjective on all old positive relations
and on all original partial-function domains. Consequently the
PRINTED forbidden-family closure applies directly to Q, with
no assumption that the FULL target-induced vertex range is
tuple-surjective or that it is function-closed.

The closure axiom gives a FULL forbidden copy P -> Q. Its
composition with the weak inclusion Q -> Target is a positive
homomorphism, but it is not automatically an EHN map, let
alone a full embedding. The *only* new transport premise below
asks precisely that every forbidden full substructure of Q
maps by an EHN map into Target. This is a LOCAL condition on
the forbidden substructures, not an assertion that the entire
weak quotient fully embeds in Target.

Under that explicit local reflection assumption, this file
constructs an actual injective forbidden EHN witness into Target
with no greater original SOURCE support on any chosen target
region, and then an injective support minimizer.

This strictly avoids the separately unproved closed +
tuple-surjective TRUE target-image conditions used by the earlier
conditional transfer. It does NOT prove that local transport
holds under the original maximal-common-lift hypotheses, nor
the unrestricted strong-amalgamation theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Local target reflection restricted to FULL forbidden
substructures of the source-generated weak-image quotient.
The quotient inclusion is only weak globally. This condition
is not implied by weak incidence preservation. -/
def ForbiddenFullWeakImagePiecesTransport
    (F : ∀ {X : Type}, Structure L X → Prop)
    {UT : Type} (Target : Structure L UT)
    (w : ForbiddenEHNWitness F Target) : Prop :=
  ∀ {Z : Type} (P : Structure L Z), F P →
    ∀ e : Structure.Embedding P
      (Structure.weakImage w.source Target w.toTarget),
      P.IsEHNHomomorphismEmbedding Target
        (fun z => (e z).1)

/-- The source-generated weak quotient supplies a forbidden FULL
substructure by the printed image-closure axiom alone.
Only the EHN transport of that specific full forbidden copy
is additional. No tuple-surjectivity of the full induced
target range, or function-range closedness, is assumed. -/
theorem forbiddenWeakImage_injectiveReplacement_of_localTransport
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (w : ForbiddenEHNWitness F Target)
    (hTransport : ForbiddenFullWeakImagePiecesTransport F Target w) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  classical
  letI : Finite w.Carrier := w.finiteCarrier
  let Q : Structure L (Set.range w.toTarget) :=
    Structure.weakImage w.source Target w.toTarget
  let q : w.Carrier → Set.range w.toTarget :=
    Structure.weakImage.quotientMap (f := w.toTarget)
  obtain ⟨hqSurj, hqHE, hqTuple⟩ :=
    originalPartialHE_weakImage_quotient_data
      w.source Target w.toTarget
      w.homEmbedding.toOriginalPartial
  obtain ⟨Z, P, hP, ⟨e⟩⟩ :=
    hImage w.source Q q w.forbidden hqHE hqTuple
  letI : Finite Z := hFiniteF P hP
  let g : Z → UT := fun z => (e z).1
  have hgInj : Function.Injective g := by
    intro z z' h
    exact e.injective (Subtype.ext h)
  let v : ForbiddenEHNWitness F Target := {
    Carrier := Z
    finiteCarrier := inferInstance
    source := P
    forbidden := hP
    toTarget := g
    homEmbedding := hTransport P hP e
  }
  let pickPreimage (z : Z) : w.Carrier :=
    Classical.choose (hqSurj (e z))
  have hSection (z : Z) : q (pickPreimage z) = e z :=
    Classical.choose_spec (hqSurj (e z))
  have hSectionInj : Function.Injective pickPreimage := by
    intro z z' h
    apply e.injective
    calc
      e z = q (pickPreimage z) := (hSection z).symm
      _ = q (pickPreimage z') := congrArg q h
      _ = e z' := hSection z'
  have hSupportEq (z : Z) :
      w.toTarget (pickPreimage z) = v.toTarget z := by
    change (q (pickPreimage z)).1 = (e z).1
    exact congrArg Subtype.val (hSection z)
  let supportMap :
      {z : Z // v.toTarget z ∈ AOnly} →
      {x : w.Carrier // w.toTarget x ∈ AOnly} :=
    fun z => ⟨pickPreimage z.1, by
      rw [hSupportEq]
      exact z.2⟩
  have hSupportInj : Function.Injective supportMap := by
    intro a b hab
    apply Subtype.ext
    exact hSectionInj (congrArg Subtype.val hab)
  have hCount :
      Nat.card {z : Z // v.toTarget z ∈ AOnly} ≤
      Nat.card {x : w.Carrier // w.toTarget x ∈ AOnly} := by
    letI : Fintype {z : Z // v.toTarget z ∈ AOnly} :=
      Fintype.ofFinite _
    letI : Fintype {x : w.Carrier // w.toTarget x ∈ AOnly} :=
      Fintype.ofFinite _
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_injective supportMap hSupportInj)
  exact ⟨v, hgInj, hCount⟩

/-- Every source-support minimizer can be injectivized under
printed tuple-image closure if the forbidden full substructures
of its genuinely tuple-surjective weak quotient transport EHN
to the actual target. The uniform local-transport premise is
separate and remains mathematically open in the maximal-lift case. -/
theorem exists_injectiveMinimalForbiddenEHNWitness_of_weakImageLocalTransport
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (hTransport : ∀ w : ForbiddenEHNWitness F Target,
      ForbiddenFullWeakImagePiecesTransport F Target w)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      ∀ w : ForbiddenEHNWitness F Target,
        v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  obtain ⟨w, hwMin⟩ :=
    exists_minimalForbiddenEHNWitness_support
      F Target AOnly hExists
  obtain ⟨v, hvInj, hBound⟩ :=
    forbiddenWeakImage_injectiveReplacement_of_localTransport
      F hFiniteF hImage Target AOnly w (hTransport w)
  refine ⟨v, hvInj, ?_⟩
  intro w'
  exact hBound.trans (hwMin w')

end AllThoseRamseyClasses.Lifts
