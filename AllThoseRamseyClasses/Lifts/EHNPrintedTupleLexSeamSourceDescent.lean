import AllThoseRamseyClasses.Lifts.EHNSeamCollisionSurjectiveSourceCount
import AllThoseRamseyClasses.Lifts.EHNPrintedTupleImageClosure
import Mathlib.Data.Fintype.Card

/-!
# Track D: actual LEXICOGRAPHIC forbidden source descent under the printed family closure

This is the exact seam-root collision counterpart of source
support descent: an actual surjective source contraction
h : Old→New may identify two distinct old source vertices
mapping to the same genuine target seam point, leaving the
PRIMARY A-only source support unchanged but decreasing the
SECONDARY count of ordered collapsed source pairs.

Given true original weak native preservation + full irreducible
source-test transport + ORIGINAL tuple-surjectivity, h is an
admissible original-partial HE source map. The printed 2019
image-closure principle gives a full forbidden source P ↪ New,
not necessarily forbiddenness of the whole New. A genuine EHN
target map g : New→Target factoring the original f produces
an actual finite forbidden EHN witness on P.

The P-source primary support does not grow: P↪New and old
source surjects to New with preserved target map. The P-source
SECONDARY ordered seam-collision count is STRICTLY smaller
than the old one: P↪New cannot add collision pairs and the
source contraction h already removes an actual old seam pair.

Thus an original source-support-first, seam-collision-second
minimal witness cannot admit such a genuine test-preserving
tuple-surjective source contraction. This uses the exact
PRINTED forbidden-family image-closure clause, not the stronger
surjective EHN image-closed condition.

This theorem DOES NOT construct the source contraction h or
the new EHN target map g from the common maximal canonical
lift. That remains the genuine unrestricted Claim 1/2 gap.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Construct a TRUE finite forbidden native EHN witness with
no larger original source A-only support and STRICTLY fewer
original ordered source seam-collision pairs, from an ACTUAL
surjective tuple-surjective full-test-preserving source
contraction collapsing an OLD pair in the common seam.

The forbidden new source is the genuine FULL forbidden copy
inside New supplied by the published tuple-image closure.
No guessed weak-image fullness or source quotient property
is used. -/
theorem forbiddenEHNWitness_lexDescent_of_printedTupleSourceContraction
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {UT : Type} (Target : Structure L UT)
    (AOnly Seam : Set UT)
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
    (a b : w.Carrier) (hab : a ≠ b)
    (hCollapse : h a = h b)
    (hSeam : w.toTarget a ∈ Seam) :
    ∃ v : ForbiddenEHNWitness F Target,
      v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly ∧
      v.seamCollisionPairCount Seam <
        w.seamCollisionPairCount Seam := by
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
  letI : Fintype {z : w.Carrier //
      w.toTarget z ∈ AOnly} := Fintype.ofFinite _
  letI : Fintype {z : W // g z ∈ AOnly} := Fintype.ofFinite _
  have hNewSupportLeOld :
      Nat.card {z : W // g z ∈ AOnly} ≤
      Nat.card {z : w.Carrier // w.toTarget z ∈ AOnly} := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_surjective
        oldSupportToNew hSupportSurj)

  let copySupport :
      {z : Z // g (e z) ∈ AOnly} →
      {z : W // g z ∈ AOnly} :=
    fun z => ⟨e z.1, z.2⟩
  have hCopyInj : Function.Injective copySupport := by
    intro z z' hEq
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val hEq)
  letI : Fintype {z : Z // g (e z) ∈ AOnly} :=
    Fintype.ofFinite _
  have hCopySupportLeNew :
      Nat.card {z : Z // g (e z) ∈ AOnly} ≤
      Nat.card {z : W // g z ∈ AOnly} := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_injective copySupport hCopyInj)
  have hPrimaryLe :
      v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly :=
    hCopySupportLeNew.trans hNewSupportLeOld

  have hNewCollisionStrict :
      Nat.card {p : W × W //
        p.1 ≠ p.2 ∧ g p.1 = g p.2 ∧ g p.1 ∈ Seam} <
      Nat.card {p : w.Carrier × w.Carrier //
        p.1 ≠ p.2 ∧
        w.toTarget p.1 = w.toTarget p.2 ∧
        w.toTarget p.1 ∈ Seam} :=
    finiteSurjectiveSourceContraction_strictSeamCollisionDrop
      h hSurj w.toTarget g hFactor
      Seam a b hab hCollapse hSeam
  have hCopyCollisionLe :
      Nat.card {p : Z × Z //
        p.1 ≠ p.2 ∧
        (g ∘ e) p.1 = (g ∘ e) p.2 ∧
        (g ∘ e) p.1 ∈ Seam} ≤
      Nat.card {p : W × W //
        p.1 ≠ p.2 ∧
        g p.1 = g p.2 ∧ g p.1 ∈ Seam} :=
    finiteSourceInjection_seamCollisionPairs_le
      e e.injective g Seam
  have hSecondaryStrict :
      v.seamCollisionPairCount Seam <
        w.seamCollisionPairCount Seam := by
    change Nat.card {p : Z × Z //
        p.1 ≠ p.2 ∧
        (g ∘ e) p.1 = (g ∘ e) p.2 ∧
        (g ∘ e) p.1 ∈ Seam} <
      Nat.card {p : w.Carrier × w.Carrier //
        p.1 ≠ p.2 ∧
        w.toTarget p.1 = w.toTarget p.2 ∧
        w.toTarget p.1 ∈ Seam}
    exact lt_of_le_of_lt hCopyCollisionLe hNewCollisionStrict
  exact ⟨v, hPrimaryLe, hSecondaryStrict⟩

/-- At a genuine original lex-minimal forbidden EHN witness
(primary SOURCE left support followed by secondary ORIGINAL
ordered seam collisions), a surjective tuple-surjective,
full-test-preserving source contraction cannot identify TWO
distinct ORIGINAL source vertices already collapsed at a
true target seam image while factoring through another
genuine EHN map to the same target.

This uses EXACT published forbidden-family tuple-image closure.
The theorem proves a contradiction IF the specified source
contraction exists. Neither its existence nor unrestricted
original Section 3 strong AP is established. -/
theorem lexMinimalForbiddenEHNWitness_no_mergedSeamSourceQuotient
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {UT : Type} (Target : Structure L UT)
    (AOnly Seam : Set UT)
    (w : ForbiddenEHNWitness F Target)
    (hPrimary : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount AOnly ≤ v.sourceSupportCount AOnly)
    (hSecondary : ∀ v : ForbiddenEHNWitness F Target,
      v.sourceSupportCount AOnly =
        w.sourceSupportCount AOnly →
      w.seamCollisionPairCount Seam ≤
        v.seamCollisionPairCount Seam)
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
    (a b : w.Carrier) (hab : a ≠ b)
    (hCollapse : h a = h b)
    (hSeam : w.toTarget a ∈ Seam) :
    False := by
  obtain ⟨v, hNoIncrease, hStrict⟩ :=
    forbiddenEHNWitness_lexDescent_of_printedTupleSourceContraction
      F hFiniteF hImage Target AOnly Seam w
      New h hSurj hWeak hTransport hTuple g hg hFactor
      a b hab hCollapse hSeam
  have hPrimaryEq :
      v.sourceSupportCount AOnly =
        w.sourceSupportCount AOnly :=
    Nat.le_antisymm hNoIncrease (hPrimary v)
  exact (Nat.not_lt_of_ge (hSecondary v hPrimaryEq)) hStrict

end AllThoseRamseyClasses.Lifts
