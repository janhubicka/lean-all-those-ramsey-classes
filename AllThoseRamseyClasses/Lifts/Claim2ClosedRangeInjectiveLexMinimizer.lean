import AllThoseRamseyClasses.Lifts.EHNClosedRangeFactorization
import AllThoseRamseyClasses.Lifts.Claim2GlobalLexSourceMinimizer
import AllThoseRamseyClasses.Lifts.ForbiddenWeakWitnessMinimization

/-!
# Injective lexicographic (A,B) weak forbidden witness on a truly closed range

The original 2019 Claim 2 proof wants one original finite
F-forbidden source weakly mapping into a fixed free target,
simultaneously minimizing total A-exclusive SOURCE support and,
among all those tied at this global A-minimum, total B-exclusive
SOURCE support. In general it cannot simply injectivize a weak
source map: its range may fail to be function closed, and the
printed tuple-surjective family image-closure condition is too
weak to produce a forbidden FULL induced range.

This module gives a correct STRONGER conditional replacement:
suppose (1) the forbidden family is closed under ACTUAL
vertex-surjective EHN images, and (2) the range of EVERY
forbidden EHN weak map into the fixed target is FUNCTION-CLOSED.

Then EVERY individual forbidden witness has an INJECTIVE
forbidden replacement in the SAME target whose total SOURCE
support count does not increase for ANY target subset.
The actual full induced closed range is the new source.

Apply that reduction to a true globally lexicographically
(A,B)-minimal source witness. Its A and B source counts
cannot decrease further, so the SAME chosen injective
replacement remains lexicographically minimal.

This is not a proof of the original printed image-closure
hypothesis, which is weaker. For function-free relational
languages the range-closedness condition is automatic;
in functional languages it requires an independent proof.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A forbidden original native weak EHN source-map witness
whose actual target range is FULL function-closed has an
injective forbidden replacement, without increasing SOURCE
support count on ANY fixed target vertex set.

Closure of F under genuine vertex-surjective EHN images
is explicit and stronger than printed tuple-image closure.
No weak-map injectivity is assumed for the input. -/
theorem forbiddenEHNWitness_injectiveReplacement_allSupport_of_closedRange
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hImageClosed :
      ∀ {X Y : Type}
        (Src : Structure L X) (Dst : Structure L Y)
        (q : X → Y),
        F Src →
        Src.IsEHNHomomorphismEmbedding Dst q →
        Function.Surjective q → F Dst)
    {UT : Type} (Target : Structure L UT)
    (w : ForbiddenEHNWitness F Target)
    (hClosed : Target.IsClosed (Set.range w.toTarget)) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      ∀ (Active : Set UT),
        v.sourceSupportCount Active ≤
          w.sourceSupportCount Active := by
  classical
  letI : Finite w.Carrier := w.finiteCarrier
  let S : Set UT := Set.range w.toTarget
  let A : Structure L S := Target.induce S hClosed
  let e : Structure.Embedding A Target :=
    Target.inclusion S hClosed
  have hForbidden : F A :=
    forbiddenFullInducedEHNImage_of_closedRange
      F hImageClosed w.source Target w.forbidden
      w.toTarget w.homEmbedding hClosed
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
  refine ⟨v, hvInjective, ?_⟩
  intro Active
  let supportMap :
      {x : w.Carrier // w.toTarget x ∈ Active} →
      {y : S // y.1 ∈ Active} :=
    fun x => ⟨q x.1, x.2⟩
  have hSupportSurjective : Function.Surjective supportMap := by
    intro y
    obtain ⟨x, hx⟩ := hqSurjective y.1
    have hxActive : w.toTarget x ∈ Active := by
      change (q x).1 ∈ Active
      rw [hx]
      exact y.2
    refine ⟨⟨x, hxActive⟩, ?_⟩
    exact Subtype.ext hx
  change Nat.card {y : S // y.1 ∈ Active} ≤
    Nat.card {x : w.Carrier // w.toTarget x ∈ Active}
  letI : Fintype {x : w.Carrier //
      w.toTarget x ∈ Active} := Fintype.ofFinite _
  letI : Fintype {y : S // y.1 ∈ Active} := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_le_of_surjective supportMap hSupportSurjective)

/-- With an explicitly CLOSED target range for every forbidden
weak EHN map, and F closed under genuine vertex-surjective EHN
images, one can choose a SINGLE INJECTIVE actual original
F-forbidden witness lexicographically minimal for the full
source counts (A-exclusive, B-exclusive).

Neither an F-source function-input test cover nor the invalid
printed range-injectivization shortcut is assumed. -/
theorem exists_injective_global_lex_minimum_forbiddenEHN_of_closedRange
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (A : Structure L X),
      F A → Finite X)
    (hImageClosed :
      ∀ {X Y : Type}
        (Src : Structure L X) (Dst : Structure L Y)
        (q : X → Y),
        F Src →
        Src.IsEHNHomomorphismEmbedding Dst q →
        Function.Surjective q → F Dst)
    {UT : Type} (Target : Structure L UT)
    (AActive BActive : Set UT)
    (hNonempty : Nonempty (ForbiddenEHNWitness F Target))
    (hClosedAll :
      ∀ w : ForbiddenEHNWitness F Target,
        Target.IsClosed (Set.range w.toTarget)) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      (∀ u : ForbiddenEHNWitness F Target,
        v.sourceSupportCount AActive ≤
          u.sourceSupportCount AActive) ∧
      (∀ u : ForbiddenEHNWitness F Target,
        u.sourceSupportCount AActive =
          v.sourceSupportCount AActive →
        v.sourceSupportCount BActive ≤
          u.sourceSupportCount BActive) := by
  obtain ⟨initial⟩ := hNonempty
  obtain ⟨W, New, hNew, hFiniteNew, g, hg,
      hMinA, hMinB⟩ :=
    exists_global_lex_minimum_weakForbiddenSource_support
      F hFiniteF Target initial.source initial.forbidden
      initial.toTarget initial.homEmbedding AActive BActive
  let w : ForbiddenEHNWitness F Target := {
    Carrier := W
    finiteCarrier := hFiniteNew
    source := New
    forbidden := hNew
    toTarget := g
    homEmbedding := hg
  }
  obtain ⟨v, hvInj, hNonIncrease⟩ :=
    forbiddenEHNWitness_injectiveReplacement_allSupport_of_closedRange
      F hImageClosed Target w (hClosedAll w)
  have hVMinA :
      ∀ u : ForbiddenEHNWitness F Target,
        v.sourceSupportCount AActive ≤
          u.sourceSupportCount AActive := by
    intro u
    calc
      v.sourceSupportCount AActive ≤
          w.sourceSupportCount AActive :=
        hNonIncrease AActive
      _ ≤ u.sourceSupportCount AActive :=
        hMinA u.source u.forbidden u.toTarget u.homEmbedding
  have hEqualA :
      v.sourceSupportCount AActive =
        w.sourceSupportCount AActive :=
    Nat.le_antisymm (hNonIncrease AActive)
      (hMinA v.source v.forbidden v.toTarget v.homEmbedding)
  refine ⟨v, hvInj, hVMinA, ?_⟩
  intro u hUA
  have hUAold :
      u.sourceSupportCount AActive =
        w.sourceSupportCount AActive :=
    hUA.trans hEqualA
  calc
    v.sourceSupportCount BActive ≤
        w.sourceSupportCount BActive :=
      hNonIncrease BActive
    _ ≤ u.sourceSupportCount BActive :=
      hMinB u.source u.forbidden u.toTarget u.homEmbedding hUAold

end AllThoseRamseyClasses.Lifts
