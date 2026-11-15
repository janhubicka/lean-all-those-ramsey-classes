import AllThoseRamseyClasses.Lifts.EHNSourceReplacementSurjectiveTestTransport
import AllThoseRamseyClasses.Lifts.EHNPrintedTupleImageClosure
import Mathlib.Data.Fintype.Card

/-!
# Track D: strict source-support descent using the PRINTED tuple-image family closure

A new source-changing step does not need the forbidden family to be
closed under arbitrary surjective EHN images. The original published
condition gives a FULL forbidden substructure P of New whenever
the old forbidden source maps into New by an original-partial
tuple-surjective homomorphism-embedding.

Assume an old forbidden EHN witness w, a new source New and an
old-to-new map h which:
* is surjective on native source vertices,
* preserves all original positive relation/function incidences,
* transports all original FULL irreducible source tests, hence is EHN,
* is tuple-surjective on original relations and function domains.

Let g : New→Target be a genuine EHN map factoring w.toTarget
through h. Then printed family closure supplies a genuine FULL
forbidden P ↪ New, whose composite target map g∘e is EHN.
The new P-source support embeds into the support of New.

If h identifies two distinct old source vertices both counted in
the chosen left-exclusive target region, the finite surjection
of old support onto New support gives a STRICT cardinal decrease.
Therefore the actual P witness has strictly less ORIGINAL source
support than w.

This is a constructive conditional use of the PRINTED forbidden
family closure, NOT a construction of h, g or tuple-surjectivity
under the original maximal-common-lift setting. No unrestricted
Claim 1/2, strong AP or Ramsey conclusion.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- ACTUAL forbidden-source replacement from the paper-shaped
tuple-image closure under an explicit tuple-surjective
source contraction h, provided h is genuinely EHN and the
new source admits a compatible EHN target map g.

Strict decrease concerns distinct ORIGINAL source vertices
mapping to the specified region, never just target-image
cardinality. The returned forbidden source is the genuine
FULL embedded forbidden copy P given by the printed closure,
not an unsupported claim that the entire New belongs to F. -/
theorem forbiddenEHNWitness_strictSourceReplacement_of_printedTupleClosure
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (w : ForbiddenEHNWitness F Target)
    {W : Type} (New : Structure L W)
    (h : w.Carrier → W)
    (hSurj : Function.Surjective h)
    (hWeak : w.source.IsWeakHomomorphism New h)
    (hTransport :
      TransportsOriginalFullIrreducibleTests w.source New h)
    (hTuple : OriginalPartialTupleSurjective w.source New h)
    (g : W → UT)
    (hg : New.IsEHNHomomorphismEmbedding Target g)
    (hFactor : ∀ z : w.Carrier, g (h z) = w.toTarget z)
    (x y : w.Carrier) (hxy : x ≠ y)
    (hxLeft : w.toTarget x ∈ AOnly)
    (hyLeft : w.toTarget y ∈ AOnly)
    (hCollapse : h x = h y) :
    ∃ v : ForbiddenEHNWitness F Target,
      v.sourceSupportCount AOnly < w.sourceSupportCount AOnly := by
  classical
  letI : Finite w.Carrier := w.finiteCarrier
  letI : Finite W := Finite.of_surjective h hSurj
  have hEHN : w.source.IsEHNHomomorphismEmbedding New h :=
    (nativeEHN_iff_weak_and_transportsFullIrreducibleTests
      w.source New h).2 ⟨hWeak, hTransport⟩
  obtain ⟨Z, P, hForbidden, ⟨e⟩⟩ :=
    hImage w.source New h w.forbidden hEHN.toOriginalPartial hTuple
  letI : Finite Z := hFiniteF P hForbidden
  let v : ForbiddenEHNWitness F Target := {
    Carrier := Z
    finiteCarrier := inferInstance
    source := P
    forbidden := hForbidden
    toTarget := g ∘ e
    homEmbedding := hg.comp e.isEHNHomomorphismEmbedding
  }

  let oldSupportToNew :
      {z : w.Carrier // w.toTarget z ∈ AOnly} →
      {z : W // g z ∈ AOnly} :=
    fun z => ⟨h z.1, by
      rw [hFactor z.1]
      exact z.2⟩
  have hSupportSurj : Function.Surjective oldSupportToNew := by
    intro z
    obtain ⟨t, ht⟩ := hSurj z.1
    have htLeft : w.toTarget t ∈ AOnly := by
      rw [← hFactor t, ht]
      exact z.2
    refine ⟨⟨t, htLeft⟩, ?_⟩
    exact Subtype.ext ht
  let sx : {z : w.Carrier // w.toTarget z ∈ AOnly} :=
    ⟨x, hxLeft⟩
  let sy : {z : w.Carrier // w.toTarget z ∈ AOnly} :=
    ⟨y, hyLeft⟩
  have hsne : sx ≠ sy := by
    intro heq
    exact hxy (congrArg Subtype.val heq)
  have hscoll : oldSupportToNew sx = oldSupportToNew sy :=
    Subtype.ext hCollapse
  letI : Fintype {z : w.Carrier //
      w.toTarget z ∈ AOnly} := Fintype.ofFinite _
  letI : Fintype {z : W // g z ∈ AOnly} := Fintype.ofFinite _
  have hNewStrict :
      Nat.card {z : W // g z ∈ AOnly} <
      Nat.card {z : w.Carrier // w.toTarget z ∈ AOnly} := by
    simpa only [Nat.card_eq_fintype_card] using
      (finiteCard_strict_of_surjective_and_colliding
        oldSupportToNew hSupportSurj sx sy hsne hscoll)

  let embedSupport :
      {z : Z // g (e z) ∈ AOnly} →
      {z : W // g z ∈ AOnly} :=
    fun z => ⟨e z.1, z.2⟩
  have hEmbedSupportInj : Function.Injective embedSupport := by
    intro z z' hEqual
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val hEqual)
  letI : Fintype {z : Z // g (e z) ∈ AOnly} := Fintype.ofFinite _
  have hCopyLe :
      Nat.card {z : Z // g (e z) ∈ AOnly} ≤
      Nat.card {z : W // g z ∈ AOnly} := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_injective embedSupport hEmbedSupportInj)
  have hStrict :
      v.sourceSupportCount AOnly < w.sourceSupportCount AOnly :=
    lt_of_le_of_lt hCopyLe hNewStrict
  exact ⟨v, hStrict⟩

/-- Genuine ORIGINAL primary support-minimizer obstruction to a
tuple-surjective native source contraction which identifies two
distinct original left-support vertices.

This is the exact Section 3 minimality contradiction whenever
a proposed source-changing repair meets the explicit contracts:
h is surjective, weak on every old native relation/function,
transports all original FULL irreducible tests, is ORIGINAL
tuple-surjective, and a genuine new EHN map g factors the
old target map through h. The PRINTED family closure suffices
to construct the strictly smaller forbidden witness.

This theorem does NOT construct h/g, assert that canonical
maximal-lift profile agreement implies tuple-surjectivity,
or remove the remaining unrestricted Claim 1/2 gap. -/
theorem minimalForbiddenEHNWitness_no_collapsingTupleSurjFullTestSourceRepair
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (w : ForbiddenEHNWitness F Target)
    (hPrimary : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount AOnly ≤ v.sourceSupportCount AOnly)
    {W : Type} (New : Structure L W)
    (h : w.Carrier → W)
    (hSurj : Function.Surjective h)
    (hWeak : w.source.IsWeakHomomorphism New h)
    (hTransport :
      TransportsOriginalFullIrreducibleTests w.source New h)
    (hTuple : OriginalPartialTupleSurjective w.source New h)
    (g : W → UT)
    (hg : New.IsEHNHomomorphismEmbedding Target g)
    (hFactor : ∀ z : w.Carrier, g (h z) = w.toTarget z)
    (x y : w.Carrier) (hxy : x ≠ y)
    (hxLeft : w.toTarget x ∈ AOnly)
    (hyLeft : w.toTarget y ∈ AOnly)
    (hCollapse : h x = h y) :
    False := by
  obtain ⟨v, hStrict⟩ :=
    forbiddenEHNWitness_strictSourceReplacement_of_printedTupleClosure
      F hFiniteF hImage Target AOnly w
      New h hSurj hWeak hTransport hTuple g hg hFactor
      x y hxy hxLeft hyLeft hCollapse
  exact (minimalForbiddenEHNWitness_no_strict_drop
    AOnly w hPrimary v) hStrict

end AllThoseRamseyClasses.Lifts
