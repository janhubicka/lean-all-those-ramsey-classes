import AllThoseRamseyClasses.Lifts.EHNClosedRangeFactorization
import AllThoseRamseyClasses.Lifts.EHNInputTestCoverageClosedRange
import AllThoseRamseyClasses.Lifts.ForbiddenWeakWitnessMinimization

/-!
# Injective forbidden minimizers under source irreducible-input coverage

The printed original Section 3 lift proof says that closure of the
forbidden family under homomorphism-embedding images allows the
initial forbidden witness to be chosen INJECTIVE. This is valid for
genuine partial/set-valued function structures only when the
original weak EHN map has a FUNCTION-CLOSED target image; otherwise
the raw weak image may not be a full target substructure.

The two separately verified lemmas now supply a legitimate
conditional repair:
* if every native function input tuple of a forbidden source
  belongs to some full irreducible source test, an arbitrary EHN
  target map has a full function-closed range;
* on such a closed range, the EHN map factors SURJECTIVELY through
  the actual native induced target, which is itself forbidden
  when the forbidden family is closed under true surjective EHN
  images. Its inclusion into the ambient target is a FULL
  injective native functional embedding.

More strongly, the induced-image witness cannot have MORE
source vertices in any specified target region: its source-support
set is the surjective image of the original source-support set.
Thus a minimum-support forbidden EHN witness may be chosen
INJECTIVE without increasing the minimum.

This repairs the exact first "we may assume f injective" move
of the printed proof UNDER THE EXPLICIT source irreducible-input
cover hypothesis, without an illegitimate weak image quotient.
The condition is NOT a consequence of the arbitrary connected
regular image-closed forbidden-family assumptions. The iterated
multicomponent Claim 2 argument remains independently open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An arbitrary finite forbidden EHN witness can be replaced by
a genuine injective forbidden witness into the SAME target without
increasing source support on ANY fixed target region, provided
all complete native function-input tuples of its source admit
a full irreducible source test, and the forbidden family is
closed under actual SURJECTIVE EHN images.

The image's carrier is the literal range subtype in Target,
with its FULL induced native relations and functions, not an
incidence-generated weak quotient. -/
theorem forbiddenEHNWitness_injectiveReplacement_of_inputTests
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hImageClosed :
      ∀ {X Y : Type}
        (Src : Structure L X) (Dst : Structure L Y)
        (q : X → Y),
        F Src →
        Src.IsEHNHomomorphismEmbedding Dst q →
        Function.Surjective q → F Dst)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (w : ForbiddenEHNWitness F Target)
    (hCovered : FunctionInputTuplesCoveredByIrreducibleTests
      w.source) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  classical
  letI : Finite w.Carrier := w.finiteCarrier
  let S : Set UT := Set.range w.toTarget
  have hSclosed : Target.IsClosed S :=
    ehn_range_isClosed_of_irreducibleInputCover
      w.source Target w.toTarget w.homEmbedding hCovered
  let A : Structure L S := Target.induce S hSclosed
  let e : Structure.Embedding A Target :=
    Target.inclusion S hSclosed
  have hForbidden : F A :=
    forbiddenFullInducedEHNImage_of_closedRange
      F hImageClosed w.source Target w.forbidden
      w.toTarget w.homEmbedding hSclosed
  let q : w.Carrier → S :=
    fun x => ⟨w.toTarget x, ⟨x, rfl⟩⟩
  have hqSurjective : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext hx⟩
  letI : Finite S := Finite.of_surjective q hqSurjective
  let v : ForbiddenEHNWitness F Target := {
    Carrier := S
    finiteCarrier := inferInstance
    source := A
    forbidden := hForbidden
    toTarget := fun y => y.1
    homEmbedding := e.isEHNHomomorphismEmbedding
  }
  have hvInjective : Function.Injective v.toTarget := by
    intro a b hab
    exact Subtype.ext hab
  let supportMap :
      {x : w.Carrier // w.toTarget x ∈ AOnly} →
      {y : S // y.1 ∈ AOnly} :=
    fun x => ⟨q x.1, x.2⟩
  have hSupportSurjective : Function.Surjective supportMap := by
    intro y
    obtain ⟨x, hx⟩ := hqSurjective y.1
    have hxSupport : w.toTarget x ∈ AOnly := by
      change (q x).1 ∈ AOnly
      rw [hx]
      exact y.2
    refine ⟨⟨x, hxSupport⟩, ?_⟩
    exact Subtype.ext hx
  have hSupportCount :
      Nat.card {y : S // y.1 ∈ AOnly} ≤
      Nat.card {x : w.Carrier // w.toTarget x ∈ AOnly} := by
    letI : Fintype {x : w.Carrier //
        w.toTarget x ∈ AOnly} := Fintype.ofFinite _
    letI : Fintype {y : S //
        y.1 ∈ AOnly} := Fintype.ofFinite _
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_surjective supportMap hSupportSurjective)
  refine ⟨v, hvInjective, ?_⟩
  change Nat.card {y : S // y.1 ∈ AOnly} ≤
    Nat.card {x : w.Carrier // w.toTarget x ∈ AOnly}
  exact hSupportCount

/-- **Minimal-support injectivization, with no image shortcut.**
When EVERY forbidden source admits the same genuine irreducible
function-input test cover, one of the actual global source-support
minimizers is an INJECTIVE forbidden EHN witness into Target.

The minimizer need not be unique, and no unqualified result is
claimed for arbitrary-arity connected forbidden sources. -/
theorem exists_injectiveMinimalForbiddenEHNWitness_of_inputTests
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hImageClosed :
      ∀ {X Y : Type}
        (Src : Structure L X) (Dst : Structure L Y)
        (q : X → Y),
        F Src →
        Src.IsEHNHomomorphismEmbedding Dst q →
        Function.Surjective q → F Dst)
    (hCovered :
      ∀ {V : Type} (A : Structure L V),
        F A → FunctionInputTuplesCoveredByIrreducibleTests A)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      ∀ w : ForbiddenEHNWitness F Target,
        v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  obtain ⟨w, hMinimal⟩ :=
    exists_minimalForbiddenEHNWitness_support
      F Target AOnly hExists
  obtain ⟨v, hvInj, hvBound⟩ :=
    forbiddenEHNWitness_injectiveReplacement_of_inputTests
      F hImageClosed Target AOnly w
      (hCovered w.source w.forbidden)
  refine ⟨v, hvInj, ?_⟩
  intro w'
  exact hvBound.trans (hMinimal w')

end AllThoseRamseyClasses.Lifts
