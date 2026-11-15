import AllThoseRamseyClasses.Lifts.EHNInjectiveSupportMinimizer
import AllThoseRamseyClasses.Lifts.GlobalForbiddenEHNAvoidance
import AllThoseRamseyClasses.Lifts.EHNPrintedTupleImageClosure

/-!
# A relational repair: saturate the forbidden family by full-range EHN images

This is NOT the original tuple-surjective image closure. We CHANGE the
forbidden family, retaining the same forbidden-free shadow class.
The new family contains every vertex-surjective EHN image of a finite
original forbidden source, whether or not all target positive tuples
come from that source. The quotient map is not claimed to be full.

In a function-free language the actual target range is closed. Thus
this saturation satisfies the stronger image-closure contract of the
existing injective-support-minimizer theorem, with no uncovered-input
hypothesis left over. The result supplies an injective, source-support
minimal forbidden witness for the REPAIRED family, not the original
canonical lift. The subsequent Claim 2 argument is a separate task.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Full-range saturation allows extra target incidences. Its witnesses
are genuine finite original EHN sources and vertex-surjective maps.
It is deliberately stronger than positive-tuple image closure. -/
def FullRangeEHNSaturation
    (F : ∀ {W : Type}, Structure L W → Prop)
    {Y : Type} (A : Structure L Y) : Prop :=
  ∃ (X : Type) (Source : Structure L X),
    Finite X ∧ F Source ∧
    ∃ q : X → Y,
      Source.IsEHNHomomorphismEmbedding A q ∧ Function.Surjective q

/-- Every finite original forbidden member belongs to the saturation. -/
theorem fullRangeEHNSaturation_of_mem
    (F : ∀ {W : Type}, Structure L W → Prop)
    {X : Type} (A : Structure L X)
    (hFinite : Finite X) (hF : F A) :
    FullRangeEHNSaturation F A := by
  exact ⟨X, A, hFinite, hF, id,
    (Structure.Embedding.id A).isEHNHomomorphismEmbedding,
    Function.surjective_id⟩

/-- Saturated members remain finite; a source carrier is not enlarged. -/
theorem finite_of_fullRangeEHNSaturation
    (F : ∀ {W : Type}, Structure L W → Prop)
    {Y : Type} (A : Structure L Y)
    (hA : FullRangeEHNSaturation F A) : Finite Y := by
  obtain ⟨X, Source, hFinite, _hF, q, _hq, hSurj⟩ := hA
  letI : Finite X := hFinite
  exact Finite.of_surjective q hSurj

/-- The stronger image closure required for honest injectivization
is automatic for the saturated family, by EHN composition. There is
NO tuple-surjectivity assumption and NO full-quotient assertion. -/
theorem fullRangeEHNSaturation_surjectiveImageClosed
    (F : ∀ {W : Type}, Structure L W → Prop)
    {X Y : Type} (Source : Structure L X) (Target : Structure L Y)
    (q : X → Y)
    (hSource : FullRangeEHNSaturation F Source)
    (hq : Source.IsEHNHomomorphismEmbedding Target q)
    (hSurj : Function.Surjective q) :
    FullRangeEHNSaturation F Target := by
  obtain ⟨Z, Original, hFinite, hF, f, hf, hfSurj⟩ := hSource
  exact ⟨Z, Original, hFinite, hF, q ∘ f,
    hq.comp hf, hSurj.comp hfSurj⟩

/-- The saturation changes the lift family but NOT the native
forbidden-free shadow class. This equivalence even holds with functions;
the function-free assumption is needed only for range normalization. -/
theorem avoids_fullRangeEHNSaturation_iff
    (F : ∀ {W : Type}, Structure L W → Prop)
    {Y : Type} (Target : Structure L Y) :
    AvoidsGlobalFunctionalEHN (FullRangeEHNSaturation F) Target ↔
      AvoidsGlobalFunctionalEHN F Target := by
  constructor
  · intro h X Source hFinite hF f hf
    exact h Source hFinite
      (fullRangeEHNSaturation_of_mem F Source hFinite hF) f hf
  · intro h X Source _hFinite hSource q hq
    obtain ⟨Z, Original, hFin, hF, f, hf, _hfSurj⟩ := hSource
    exact h Original hFin hF (q ∘ f) (hq.comp hf)

/-- A uniform original vertex bound also bounds all saturated members.
For a finite relational signature this gives finitely many isomorphism
types of saturated members; that final counting consequence is not
asserted as a separate theorem in this module. -/
theorem fullRangeEHNSaturation_card_le
    (F : ∀ {W : Type}, Structure L W → Prop) (N : ℕ)
    (hBound : ∀ {X : Type} (A : Structure L X),
      F A → Nat.card X ≤ N)
    {Y : Type} (A : Structure L Y)
    (hA : FullRangeEHNSaturation F A) : Nat.card Y ≤ N := by
  obtain ⟨X, Source, hFinite, hF, q, _hq, hSurj⟩ := hA
  letI : Finite X := hFinite
  letI : Finite Y := Finite.of_surjective q hSurj
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype Y := Fintype.ofFinite Y
  have hCard : Nat.card Y ≤ Nat.card X := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_surjective q hSurj)
  exact hCard.trans (hBound Source hF)

section Relational
variable [IsEmpty L.FuncSymbol]

/-- Unlike the unsaturated family, the repaired relational family
really has the printed closure property. Factor through the FULL
induced target range, not the positive-incidence weak image. -/
theorem fullRangeEHNSaturation_printedImageClosed
    (F : ∀ {W : Type}, Structure L W → Prop) :
    HasTupleSurjectiveForbiddenImageClosure
      (FullRangeEHNSaturation F) := by
  intro X Y Source Target q hSource hHE _hTuple
  let S : Set Y := Set.range q
  have hClosed : Target.IsClosed S := by
    intro G
    exact isEmptyElim G
  let Q : Structure L S := Target.induce S hClosed
  let g : X → S := fun x => ⟨q x, ⟨x, rfl⟩⟩
  have hg : Source.IsEHNHomomorphismEmbedding Q g := by
    exact ehn_codRestrict_functionClosed Source Target q hHE.toEHN
      S hClosed (fun x => ⟨x, rfl⟩)
  have hSurj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext hx⟩
  have hQ : FullRangeEHNSaturation F Q :=
    fullRangeEHNSaturation_surjectiveImageClosed
      F Source Q g hSource hg hSurj
  exact ⟨S, Q, hQ, ⟨Target.inclusion S hClosed⟩⟩

/-- Genuine injective replacement for the REPAIRED family, with
nonincreasing ORIGINAL-source support. The native image is full
because relational target ranges are automatically closed. -/
theorem saturatedRelationalWitness_injectiveReplacement
    (F : ∀ {W : Type}, Structure L W → Prop)
    {Y : Type} (Target : Structure L Y) (AOnly : Set Y)
    (w : ForbiddenEHNWitness (FullRangeEHNSaturation F) Target) :
    ∃ v : ForbiddenEHNWitness (FullRangeEHNSaturation F) Target,
      Function.Injective v.toTarget ∧
      v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  apply forbiddenEHNWitness_injectiveReplacement_of_inputTests
    (FullRangeEHNSaturation F)
    (fullRangeEHNSaturation_surjectiveImageClosed F) Target AOnly w
  intro G
  exact isEmptyElim G

/-- From any original finite forbidden witness obtain an INJECTIVE
support-minimal witness for the saturated family in the SAME target.
The minimization ranges over all saturated forbidden sources; it is
not an unproved recolouring of the original source carrier. -/
theorem exists_saturatedRelational_injectiveMinimizer
    (F : ∀ {W : Type}, Structure L W → Prop)
    {Y : Type} (Target : Structure L Y) (AOnly : Set Y)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ v : ForbiddenEHNWitness (FullRangeEHNSaturation F) Target,
      Function.Injective v.toTarget ∧
      ∀ w : ForbiddenEHNWitness (FullRangeEHNSaturation F) Target,
        v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  obtain ⟨w⟩ := hExists
  let lifted : ForbiddenEHNWitness (FullRangeEHNSaturation F) Target := {
    Carrier := w.Carrier
    finiteCarrier := w.finiteCarrier
    source := w.source
    forbidden := fullRangeEHNSaturation_of_mem
      F w.source w.finiteCarrier w.forbidden
    toTarget := w.toTarget
    homEmbedding := w.homEmbedding
  }
  exact exists_injectiveMinimalForbiddenEHNWitness_of_inputTests
    (FullRangeEHNSaturation F)
    (fullRangeEHNSaturation_surjectiveImageClosed F)
    (fun A _hA G => isEmptyElim G)
    Target AOnly ⟨lifted⟩

end Relational
end AllThoseRamseyClasses.Lifts
