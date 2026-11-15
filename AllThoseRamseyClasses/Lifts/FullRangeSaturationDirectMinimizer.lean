import AllThoseRamseyClasses.Lifts.FullRangeSaturationNormalForm

/-!
# Direct full-range normalization of a support-minimal saturated witness

The existing repaired relational minimizer was obtained by first
injectivizing a support-minimal EHN witness, then taking its full
induced range. This file proves the simpler direct route:

* minimize source support over the SATURATED forbidden family;
* factor the minimum EHN witness onto the FULL induced target range;
* use surjective-EHN closure of saturation;
* count the actual original source support using a surjection from
  its support subtype onto the support subtype of the full image;
* conclude that the full embedded range remains a minimum.

There is NO requirement of global injectivity, root-injectivity,
tuple-surjectivity, a source irreducible-input test cover, or a
smaller/modified source under the original unsaturated family.
The language is function-free, ensuring native target range closure.
The target may be infinite, though each forbidden witness is finite.

This is a direct alternative proof of an endpoint already stated
in FullRangeSaturationNormalForm. It is not a Ramsey/strong-AP proof.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} [IsEmpty L.FuncSymbol]

/-- A direct construction of an actually FULL embedded saturated
forbidden witness whose ORIGINAL source-vertex support is minimal
among ALL EHN witnesses from the saturated family.

No preliminary injective normal form or irreducible-input-test
cover lemma is needed: the support-count inequality is obtained
from the explicit surjection of finite SUPPORT SUBTYPES. -/
theorem exists_saturatedRelational_directFullSupportMinimizer
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UT : Type} (Target : Structure L UT) (AOnly : Set UT)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ w : ForbiddenEHNWitness (FullRangeEHNSaturation F) Target,
      (∃ e : Structure.Embedding w.source Target,
        ∀ x : w.Carrier, e x = w.toTarget x) ∧
      ∀ v : ForbiddenEHNWitness (FullRangeEHNSaturation F) Target,
        w.sourceSupportCount AOnly ≤ v.sourceSupportCount AOnly := by
  classical
  obtain ⟨w0⟩ := hExists
  let w0Sat : ForbiddenEHNWitness
      (FullRangeEHNSaturation F) Target := {
    Carrier := w0.Carrier
    finiteCarrier := w0.finiteCarrier
    source := w0.source
    forbidden := fullRangeEHNSaturation_of_mem
      F w0.source w0.finiteCarrier w0.forbidden
    toTarget := w0.toTarget
    homEmbedding := w0.homEmbedding
  }
  obtain ⟨w, hMin⟩ :=
    exists_minimalForbiddenEHNWitness_support
      (FullRangeEHNSaturation F) Target AOnly ⟨w0Sat⟩
  letI : Finite w.Carrier := w.finiteCarrier
  let S : Set UT := Set.range w.toTarget
  have hSclosed : Target.IsClosed S := by
    intro G
    exact isEmptyElim G
  let Q : Structure L S := Target.induce S hSclosed
  let q : w.Carrier → S :=
    fun x => ⟨w.toTarget x, ⟨x, rfl⟩⟩
  obtain ⟨hq, hSurj⟩ :=
    ehn_closedRange_surjectiveInducedFactor
      w.source Target w.toTarget w.homEmbedding hSclosed
  have hQ : FullRangeEHNSaturation F Q :=
    fullRangeEHNSaturation_surjectiveImageClosed
      F w.source Q q w.forbidden hq hSurj
  letI : Finite S := finite_of_fullRangeEHNSaturation F Q hQ
  let e : Structure.Embedding Q Target :=
    Target.inclusion S hSclosed
  let v : ForbiddenEHNWitness
      (FullRangeEHNSaturation F) Target := {
    Carrier := S
    finiteCarrier := finite_of_fullRangeEHNSaturation F Q hQ
    source := Q
    forbidden := hQ
    toTarget := e
    homEmbedding := e.isEHNHomomorphismEmbedding
  }
  let supportMap :
      {x : w.Carrier // w.toTarget x ∈ AOnly} →
      {y : S // y.1 ∈ AOnly} :=
    fun x => ⟨q x.1, x.2⟩
  have hSupportSurj : Function.Surjective supportMap := by
    intro y
    obtain ⟨x, hx⟩ := hSurj y.1
    have hxSupport : w.toTarget x ∈ AOnly := by
      change (q x).1 ∈ AOnly
      rw [hx]
      exact y.2
    refine ⟨⟨x, hxSupport⟩, ?_⟩
    exact Subtype.ext hx
  have hSupportBound :
      Nat.card {y : S // y.1 ∈ AOnly} ≤
        Nat.card {x : w.Carrier // w.toTarget x ∈ AOnly} := by
    letI : Fintype {x : w.Carrier //
        w.toTarget x ∈ AOnly} := Fintype.ofFinite _
    letI : Fintype {y : S // y.1 ∈ AOnly} := Fintype.ofFinite _
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_surjective supportMap hSupportSurj)
  refine ⟨v, ⟨e, fun _ => rfl⟩, ?_⟩
  intro z
  have hvw :
      v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
    change Nat.card {y : S // y.1 ∈ AOnly} ≤
      Nat.card {x : w.Carrier // w.toTarget x ∈ AOnly}
    exact hSupportBound
  exact hvw.trans (hMin z)

end AllThoseRamseyClasses.Lifts
