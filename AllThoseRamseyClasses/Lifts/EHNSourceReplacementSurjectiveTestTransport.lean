import AllThoseRamseyClasses.Lifts.EHNOriginalFullTestTransportFirewall
import AllThoseRamseyClasses.Lifts.ForbiddenWeakWitnessMinimization
import Mathlib.Data.Fintype.Card

/-!
# Track D: real forbidden EHN source replacement from surjective test transport

Fix an actual finite forbidden EHN source witness w : F → Target.
Suppose h:Old→New is a SURJECTIVE original native weak map
transporting every genuinely FULL irreducible source test; hence
h is a genuine EHN map. Under an EXPLICIT stronger assumption
that F is closed under SURJECTIVE native EHN images, New is
itself forbidden. If g:New→Target is EHN and g∘h=w.toTarget,
the NEW genuine source with map g forms a finite forbidden
EHN witness with no increase in original SOURCE support count.

This result constructs a new witness, but does not produce h/g
from the maximal-common-lift geometry and does not derive the
extra surjective image-closure premise from the published
weaker tuple-surjective image-closure hypothesis. Strict
descent and unrestricted Section 3 remain open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Construct an ACTUAL replacement forbidden EHN witness
on a possibly different finite source carrier. Unlike an
arbitrary weak image quotient, its forbiddenness follows
from a genuinely stated surjective EHN-image closure axiom
for the forbidden family, not merely tuple-image closure.
Its original source-support cannot exceed the old support. -/
theorem forbiddenEHNWitness_sourceReplacement_of_surjectiveTestTransport
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hSurjImageClosed :
      ∀ {X Y : Type}
        (Src : Structure L X) (Dst : Structure L Y)
        (q : X → Y),
        F Src →
        Src.IsEHNHomomorphismEmbedding Dst q →
        Function.Surjective q → F Dst)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (w : ForbiddenEHNWitness F Target)
    {W : Type} (New : Structure L W)
    (h : w.Carrier → W)
    (hSurj : Function.Surjective h)
    (hWeak : w.source.IsWeakHomomorphism New h)
    (hTransport :
      TransportsOriginalFullIrreducibleTests w.source New h)
    (g : W → UT)
    (hg : New.IsEHNHomomorphismEmbedding Target g)
    (hFactor : ∀ x : w.Carrier, g (h x) = w.toTarget x) :
    ∃ v : ForbiddenEHNWitness F Target,
      v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  classical
  letI : Finite w.Carrier := w.finiteCarrier
  letI : Finite W := Finite.of_surjective h hSurj
  have hEHN : w.source.IsEHNHomomorphismEmbedding New h :=
    (nativeEHN_iff_weak_and_transportsFullIrreducibleTests
      w.source New h).2 ⟨hWeak, hTransport⟩
  have hNewForbidden : F New :=
    hSurjImageClosed w.source New h w.forbidden hEHN hSurj
  let v : ForbiddenEHNWitness F Target := {
    Carrier := W
    finiteCarrier := inferInstance
    source := New
    forbidden := hNewForbidden
    toTarget := g
    homEmbedding := hg
  }
  let hSupport :
      {x : w.Carrier // w.toTarget x ∈ AOnly} →
      {y : W // g y ∈ AOnly} :=
    fun x => ⟨h x.1, by
      rw [hFactor x.1]
      exact x.2⟩
  have hSupportSurj : Function.Surjective hSupport := by
    intro y
    obtain ⟨x, hx⟩ := hSurj y.1
    have hxIn : w.toTarget x ∈ AOnly := by
      rw [← hFactor x, hx]
      exact y.2
    refine ⟨⟨x, hxIn⟩, ?_⟩
    apply Subtype.ext
    exact hx
  letI : Fintype {x : w.Carrier //
      w.toTarget x ∈ AOnly} := Fintype.ofFinite _
  letI : Fintype {y : W // g y ∈ AOnly} := Fintype.ofFinite _
  have hSupportBound :
      Nat.card {y : W // g y ∈ AOnly} ≤
      Nat.card {x : w.Carrier // w.toTarget x ∈ AOnly} := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_surjective hSupport hSupportSurj)
  exact ⟨v, hSupportBound⟩

end AllThoseRamseyClasses.Lifts
