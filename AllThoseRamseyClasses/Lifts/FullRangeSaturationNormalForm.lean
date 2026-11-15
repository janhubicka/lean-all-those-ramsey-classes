import AllThoseRamseyClasses.Lifts.FullRangeEHNSaturation

/-!
# Exact full-image normal forms for the repaired forbidden presentation

The family is explicitly changed to FullRangeEHNSaturation F. For a
function-closed actual target range, an original forbidden EHN map
factors through a FULL target substructure belonging to that saturation.
In a relational language every range is closed, giving the exact equality
Forb_EHN(F) = Forb_full_embeddings(FullRangeEHNSaturation F).

This is not an equality of the original and repaired canonical lifts.
It does not assert regularity for an infinite family, nor strong AP.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The actual full induced image, not the source-generated weak quotient,
is saturated whenever the range is closed. The original source is finite. -/
theorem originalForbiddenEHN_fullClosedImage_isSaturated
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V UT : Type} (Source : Structure L V) (Target : Structure L UT)
    (hFinite : Finite V) (hF : F Source)
    (f : V → UT) (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (hClosed : Target.IsClosed (Set.range f)) :
    FullRangeEHNSaturation F (Target.induce (Set.range f) hClosed) := by
  obtain ⟨hFactor, hSurj⟩ :=
    ehn_closedRange_surjectiveInducedFactor Source Target f hf hClosed
  exact ⟨V, Source, hFinite, hF,
    (fun x => (⟨f x, ⟨x, rfl⟩⟩ : Set.range f)), hFactor, hSurj⟩

/-- Taking full-range EHN saturation a second time adds no members.
This uses native EHN composition; it is valid also with functions. -/
theorem fullRangeEHNSaturation_idempotent
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V : Type} (A : Structure L V) :
    FullRangeEHNSaturation (FullRangeEHNSaturation F) A ↔
      FullRangeEHNSaturation F A := by
  constructor
  · rintro ⟨W, B, _hFinite, hB, f, hf, hSurj⟩
    exact fullRangeEHNSaturation_surjectiveImageClosed F B A f hB hf hSurj
  · intro hA
    exact fullRangeEHNSaturation_of_mem (FullRangeEHNSaturation F) A
      (finite_of_fullRangeEHNSaturation F A hA) hA

/-- Saturation is the least enlargement containing the finite original
members and closed under vertex-surjective native EHN images. -/
theorem fullRangeEHNSaturation_le_of_surjectiveImageClosed
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hContains : ∀ {V : Type} (A : Structure L V),
      Finite V → F A → K A)
    (hClosed : ∀ {V W : Type} (A : Structure L V) (B : Structure L W)
      (f : V → W), K A → A.IsEHNHomomorphismEmbedding B f →
      Function.Surjective f → K B)
    {W : Type} (B : Structure L W)
    (hSat : FullRangeEHNSaturation F B) : K B := by
  rcases hSat with ⟨V, A, hFinite, hF, f, hf, hSurj⟩
  exact hClosed A B f (hContains A hFinite hF) hf hSurj

section Relational
variable [IsEmpty L.FuncSymbol]

/-- Exact repaired shadow theorem. Every original forbidden EHN witness
yields a FULL saturated forbidden substructure, and conversely.
No bounded-family, finite-target or tuple-surjectivity assumption. -/
theorem avoidsOriginalEHN_iff_noFullSaturatedSubstructure
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UT : Type} (Target : Structure L UT) :
    AvoidsGlobalFunctionalEHN F Target ↔
      ¬ ContainsFullForbiddenSubstructure (FullRangeEHNSaturation F) Target := by
  constructor
  · intro hAvoid hFull
    rcases hFull with ⟨V, Source, hSat, ⟨e⟩⟩
    have hSatAvoid :
        AvoidsGlobalFunctionalEHN (FullRangeEHNSaturation F) Target :=
      (avoids_fullRangeEHNSaturation_iff F Target).2 hAvoid
    exact hSatAvoid Source (finite_of_fullRangeEHNSaturation F Source hSat)
      hSat e e.isEHNHomomorphismEmbedding
  · intro hNoFull V Source hFinite hF f hf
    have hClosed : Target.IsClosed (Set.range f) := by
      intro G
      exact isEmptyElim G
    have hSat := originalForbiddenEHN_fullClosedImage_isSaturated
      F Source Target hFinite hF f hf hClosed
    exact hNoFull ⟨Set.range f, Target.induce (Set.range f) hClosed,
      hSat, ⟨Target.inclusion (Set.range f) hClosed⟩⟩

/-- Full embeddings can be obtained at the genuine global source-support
minimum over the REPAIRED family, not just injective weak maps.
The original family supplies existence; all minimization comparisons
are explicitly over the saturated family in the same actual target. -/
theorem exists_saturatedRelational_fullEmbeddingMinimizer
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UT : Type} (Target : Structure L UT) (AOnly : Set UT)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ w : ForbiddenEHNWitness (FullRangeEHNSaturation F) Target,
      (∃ e : Structure.Embedding w.source Target,
        ∀ x : w.Carrier, e x = w.toTarget x) ∧
      ∀ v : ForbiddenEHNWitness (FullRangeEHNSaturation F) Target,
        w.sourceSupportCount AOnly ≤ v.sourceSupportCount AOnly := by
  classical
  obtain ⟨w, hInjective, hMin⟩ :=
    exists_saturatedRelational_injectiveMinimizer F Target AOnly hExists
  letI : Finite w.Carrier := w.finiteCarrier
  let S : Set UT := Set.range w.toTarget
  have hClosed : Target.IsClosed S := by
    intro G
    exact isEmptyElim G
  let Q : Structure L S := Target.induce S hClosed
  let q : w.Carrier → S := fun x => ⟨w.toTarget x, ⟨x, rfl⟩⟩
  have hSurj : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, Subtype.ext hx⟩
  have hFactor : w.source.IsEHNHomomorphismEmbedding Q q :=
    (ehn_closedRange_surjectiveInducedFactor
      w.source Target w.toTarget w.homEmbedding hClosed).1
  have hQ : FullRangeEHNSaturation F Q :=
    fullRangeEHNSaturation_surjectiveImageClosed
      F w.source Q q w.forbidden hFactor hSurj
  let e : Structure.Embedding Q Target := Target.inclusion S hClosed
  let v : ForbiddenEHNWitness (FullRangeEHNSaturation F) Target := {
    Carrier := S
    finiteCarrier := finite_of_fullRangeEHNSaturation F Q hQ
    source := Q
    forbidden := hQ
    toTarget := e
    homEmbedding := e.isEHNHomomorphismEmbedding
  }
  let supportEquiv : {x : w.Carrier // w.toTarget x ∈ AOnly} ≃
      {y : S // y.1 ∈ AOnly} :=
    Equiv.ofBijective
      (fun x => ⟨q x.1, x.2⟩)
      ⟨(by
          intro x y hxy
          apply Subtype.ext
          apply hInjective
          exact congrArg (fun z : {s : S // s.1 ∈ AOnly} => z.1.1) hxy),
        (by
          intro y
          obtain ⟨x, hx⟩ := hSurj y.1
          have hSupport : w.toTarget x ∈ AOnly := by
            change (q x).1 ∈ AOnly
            rw [hx]
            exact y.2
          exact ⟨⟨x, hSupport⟩, Subtype.ext hx⟩)⟩
  have hCount : v.sourceSupportCount AOnly = w.sourceSupportCount AOnly := by
    change Nat.card {y : S // y.1 ∈ AOnly} =
      Nat.card {x : w.Carrier // w.toTarget x ∈ AOnly}
    exact (Nat.card_congr supportEquiv).symm
  refine ⟨v, ⟨e, fun _ => rfl⟩, ?_⟩
  intro z
  rw [hCount]
  exact hMin z

end Relational
end AllThoseRamseyClasses.Lifts
