import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram
import AllThoseRamseyClasses.Lifts.Claim2ActualOuterBActiveCard
import Mathlib.Data.Fintype.Card

/-!
# Source-side quantitative barrier to keeping original A-support minimality

An actual B-to-A selected-Q native source flip agrees with the
original weak EHN target map on the ENTIRE old full complement E.
If every OLD A-exclusive SOURCE vertex belongs to that complement,
the full complement embedding already injects all old A-support
SOURCE vertices into the NEW A-support SOURCE vertices.

If the inserted Q has even ONE A-exclusive nonroot vertex, its
new image lies OUTSIDE the full new complement embedding by the
literal free-amalgam overlap property. Consequently the NEW total
A-exclusive SOURCE count is STRICTLY GREATER than the OLD one.

This is a genuinely source-cardinality obstruction, not target-image
counting and not a proof that every B-to-A flip introduces such
a nonroot A-exclusive vertex. It shows exactly why original GLOBAL
A-source-support minimality is NOT an automatic invariant of the
B-rank-decreasing selected-Q step.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- If all original A-active SOURCE vertices lie in the old
retained full complement, old/new target values agree there,
and some NEW A-active SOURCE vertex lies outside the new
complement image, then total A-active SOURCE support strictly
INCREASES on finite sources.

No assumptions on source-map injectivity or native source
geometry beyond the two full complement embeddings. -/
theorem fullNativeRetainedComplement_Aactive_strictIncrease
    {V W E UT : Type}
    {Old : Structure L V} {New : Structure L W}
    {Complement : Structure L E}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (f : V → UT) (flip : W → UT)
    (AActive : Set UT)
    (hFiniteOld : Finite V) (hFiniteNew : Finite W)
    (hOldAllAInE : ∀ v : V, f v ∈ AActive →
      v ∈ Set.range iOldE)
    (hEAgree : ∀ e : E, flip (iNewE e) = f (iOldE e))
    (newA : W)
    (hNewA : flip newA ∈ AActive)
    (hNewOutsideE : newA ∉ Set.range iNewE) :
    Nat.card {v : V // f v ∈ AActive} <
      Nat.card {w : W // flip w ∈ AActive} := by
  classical
  letI : Finite V := hFiniteOld
  letI : Finite W := hFiniteNew
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype W := Fintype.ofFinite W
  let repr : {v : V // f v ∈ AActive} → E :=
    fun v => Classical.choose (hOldAllAInE v.1 v.2)
  have hRepr :
      ∀ v : {v : V // f v ∈ AActive},
        iOldE (repr v) = v.1 := by
    intro v
    exact Classical.choose_spec (hOldAllAInE v.1 v.2)
  let inj :
      {v : V // f v ∈ AActive} ↪
        {w : W // flip w ∈ AActive} := {
    toFun := fun v => ⟨iNewE (repr v), by
      rw [hEAgree (repr v), hRepr v]
      exact v.2⟩
    inj' := by
      intro v v' hvv'
      have hE : repr v = repr v' :=
        iNewE.injective (congrArg (fun w : {w : W // flip w ∈ AActive} => (w : W)) hvv')
      apply Subtype.ext
      calc
        v.1 = iOldE (repr v) := (hRepr v).symm
        _ = iOldE (repr v') := congrArg iOldE hE
        _ = v'.1 := hRepr v'
  }
  have hNotSurj : ¬ Function.Surjective inj := by
    intro hSurj
    obtain ⟨v, hv⟩ := hSurj
      (⟨newA, hNewA⟩ : {w : W // flip w ∈ AActive})
    exact hNewOutsideE ⟨repr v,
      congrArg (fun w : {w : W // flip w ∈ AActive} => (w : W)) hv⟩
  have hStrict :
      Fintype.card {v : V // f v ∈ AActive} <
      Fintype.card {w : W // flip w ∈ AActive} :=
    Fintype.card_lt_of_injective_not_surjective
      inj inj.injective hNotSurj
  simpa only [Nat.card_eq_fintype_card] using hStrict

/-- In a genuine selected-Q native free amalgam, a Q SOURCE
vertex outside the full ordered Q root cannot lie in the image
of the retained complementary E side. This is the ACTUAL
full-source overlap equation, not a weak target-map inference. -/
theorem fullNativeSelectedQ_nonroot_outside_retainedComplement
    {W Q E R : Type}
    {New : Structure L W}
    {Replacement : Structure L Q}
    {Complement : Structure L E}
    {Root : Structure L R}
    (sQ : Structure.Embedding Root Replacement)
    (sE : Structure.Embedding Root Complement)
    (iQ : Structure.Embedding Replacement New)
    (iE : Structure.Embedding Complement New)
    (hFree : Structure.IsFreeAmalgam sQ sE iQ iE)
    (q : Q)
    (hqNonroot : q ∉ Set.range sQ) :
    iQ q ∉ Set.range iE := by
  rintro ⟨e, he⟩
  have hOver : iQ q = iE e := he.symm
  obtain ⟨r, hrQ, _hrE⟩ := (hFree.overlap q e).mp hOver
  exact hqNonroot ⟨r, hrQ.symm⟩

/-- For the ACTUAL geometric selected-Q flip, if its old
removed inner component is A-FREE and it inserts at least
one Q-nonroot SOURCE vertex mapped A-exclusive, the NEW total
A-exclusive SOURCE support is strictly GREATER.

The genuine native Q+E free amalgam certifies the inserted
nonroot vertex is NOT an old retained E vertex. This is the
precise quantitative reason why a B-decreasing replacement
may fail to remain globally A-source-minimal. -/
theorem geometricSelectedQ_AactiveNonroot_forces_strictAIncrease
    {V W UT : Type}
    (Old : Structure L V) (hFiniteOld : Finite V)
    {m : ℕ}
    (inner : GeometricFunctionalPieceData Old m)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (New : Structure L W) (hFiniteNew : Finite W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (f : V → UT) (flip : W → UT) (AActive : Set UT)
    (hOldInnerNoA : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left → f z ∉ AActive)
    (hEAgree : ∀ e : (geometricGlobalComplementChart Old inner).Carrier,
      flip (iE e) = f e.1)
    (q : Q.Carrier)
    (hqNonroot : q ∉ Set.range Q.rootEmbedding)
    (hqA : flip (iQ q) ∈ AActive) :
    Nat.card {v : V // f v ∈ AActive} <
      Nat.card {w : W // flip w ∈ AActive} := by
  let iOldE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range inner.roots) inner.minimal.1 inner.left
  have hOldAllAInE : ∀ v : V, f v ∈ AActive →
      v ∈ Set.range iOldE := by
    intro v hvA
    have hvNotInner : v ∉ functionalComponentFrom Old
        (Set.range inner.roots) inner.left := by
      intro hvInner
      exact hOldInnerNoA v hvInner hvA
    exact ⟨⟨v, hvNotInner⟩, rfl⟩
  have hNewOutsideE : iQ q ∉ Set.range iE := by
    rintro ⟨e, he⟩
    have hOver : iQ q = iE e := he.symm
    obtain ⟨r, hrQ, _hrE⟩ :=
      (hNewFree.overlap q e).mp hOver
    exact hqNonroot ⟨r, hrQ.symm⟩
  exact fullNativeRetainedComplement_Aactive_strictIncrease
    iOldE iE f flip AActive hFiniteOld hFiniteNew
    hOldAllAInE hEAgree (iQ q) hqA hNewOutsideE

/-- If an actual selected-Q replacement of an OLD A-free selected
component does NOT increase total A-exclusive SOURCE support,
then EVERY genuinely new nonroot Q vertex must be A-inactive.

This necessary criterion makes the missing original A-support
preservation obligation explicit. It is not a construction
of such an A-neutral selected-Q replacement. -/
theorem geometricSelectedQ_nonIncreasingA_forces_nonroot_Afree
    {V W UT : Type}
    (Old : Structure L V) (hFiniteOld : Finite V)
    {m : ℕ}
    (inner : GeometricFunctionalPieceData Old m)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (New : Structure L W) (hFiniteNew : Finite W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (f : V → UT) (flip : W → UT) (AActive : Set UT)
    (hOldInnerNoA : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left → f z ∉ AActive)
    (hEAgree : ∀ e : (geometricGlobalComplementChart Old inner).Carrier,
      flip (iE e) = f e.1)
    (hANonIncreasing :
      Nat.card {w : W // flip w ∈ AActive} ≤
        Nat.card {v : V // f v ∈ AActive})
    (q : Q.Carrier)
    (hqNonroot : q ∉ Set.range Q.rootEmbedding) :
    flip (iQ q) ∉ AActive := by
  intro hqA
  have hStrict :
      Nat.card {v : V // f v ∈ AActive} <
        Nat.card {w : W // flip w ∈ AActive} :=
    geometricSelectedQ_AactiveNonroot_forces_strictAIncrease
      Old hFiniteOld inner Q New hFiniteNew
      iQ iE hNewFree f flip AActive
      hOldInnerNoA hEAgree q hqNonroot hqA
  exact (Nat.not_lt_of_ge hANonIncreasing) hStrict


end AllThoseRamseyClasses.Lifts
