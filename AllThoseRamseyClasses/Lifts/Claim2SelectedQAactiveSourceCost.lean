import AllThoseRamseyClasses.Lifts.Claim2SelectedQAactiveSourcePartition
import Mathlib.Data.Set.Card

/-!
# Exact A-active SOURCE support cost of a native selected-Q replacement

The disjoint source partition of full Q +_R E gluing admits an
exact NATURAL NUMBER cardinality formula on a finite new source:

  new Active SOURCE count
    = retained E Active SOURCE count
      + inserted private-Q Active SOURCE count.

For the actual geometric B->A flip of an OLD A-FREE selected
component, every old Active SOURCE vertex belongs to E and the
weak target map agrees exactly on E. Hence the formula becomes:

  new total A-exclusive SOURCE rank
    = old total A-exclusive SOURCE rank
      + new Q-nonroot A-exclusive SOURCE rank.

This is stronger than merely detecting strict support increase:
the additive term is the exact cost of the newly inserted
native source vertices, and might support a valid weighted/
amortized well-founded descent. No target-image quotient,
old/new weak-map injectivity, or arbitrary Q selection is assumed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- For a finite full native Q+_R E source and any target
set Active, count the actual new Active SOURCE vertices as
the disjoint union of retained E and Q-PRIVATE Active SOURCE
vertices. The source maps iE and iQ are full embeddings. -/
theorem fullNativeSelectedQ_Aactive_support_card_add
    {W Q E R UT : Type}
    {New : Structure L W}
    {Replacement : Structure L Q}
    {Complement : Structure L E}
    {Root : Structure L R}
    (sQ : Structure.Embedding Root Replacement)
    (sE : Structure.Embedding Root Complement)
    (iQ : Structure.Embedding Replacement New)
    (iE : Structure.Embedding Complement New)
    (hFree : Structure.IsFreeAmalgam sQ sE iQ iE)
    (flip : W → UT) (Active : Set UT)
    (hFiniteNew : Finite W) :
    Nat.card {w : W // flip w ∈ Active} =
      Nat.card {e : E // flip (iE e) ∈ Active} +
      Nat.card {q : Q // q ∉ Set.range sQ ∧
        flip (iQ q) ∈ Active} := by
  classical
  letI : Finite W := hFiniteNew
  have hPartition :=
    fullNativeSelectedQ_Aactive_support_partition
      sQ sE iQ iE hFree flip Active
  have hDisjoint :=
    fullNativeSelectedQ_Aactive_partition_disjoint
      sQ sE iQ iE hFree flip Active
  change Nat.card (↑({w : W | flip w ∈ Active} : Set W)) =
    Nat.card (↑({e : E | flip (iE e) ∈ Active} : Set E)) +
      Nat.card (↑({q : Q |
        q ∉ Set.range sQ ∧ flip (iQ q) ∈ Active} : Set Q))
  simp only [Nat.card_coe_set_eq]
  rw [hPartition]
  rw [Set.ncard_union_eq hDisjoint]
  rw [Set.ncard_image_of_injective _ iE.injective]
  rw [Set.ncard_image_of_injective _ iQ.injective]

/-- Specialize the source cardinality addition formula to the
ACTUAL full geometric selected-Q replacement, rewriting the E
term in ORIGINAL target coordinates using full complement
agreement. The old removed component need not be A-free yet. -/
theorem geometricSelectedQ_Aactive_support_card_add_retained
    {V W UT : Type}
    (Old : Structure L V)
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
    (f : V → UT) (flip : W → UT) (Active : Set UT)
    (hEAgree :
      ∀ e : (geometricGlobalComplementChart Old inner).Carrier,
        flip (iE e) = f e.1) :
    Nat.card {w : W // flip w ∈ Active} =
      Nat.card {e : (geometricGlobalComplementChart Old inner).Carrier //
        f e.1 ∈ Active} +
      Nat.card {q : Q.Carrier //
        q ∉ Set.range Q.rootEmbedding ∧ flip (iQ q) ∈ Active} := by
  have hCard :=
    fullNativeSelectedQ_Aactive_support_card_add
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE hNewFree flip Active hFiniteNew
  simpa only [hEAgree] using hCard

/-- For an OLD selected component containing no A-active
SOURCE vertex, the actual old total A-support is exactly
the A-support on its FULL retained-complement source E.
This does not require global old weak-map injection. -/
theorem geometricSelectedQ_old_Afree_retained_Acard
    {V UT : Type}
    (Old : Structure L V)
    {m : ℕ}
    (inner : GeometricFunctionalPieceData Old m)
    (f : V → UT) (Active : Set UT)
    (hOldInnerNoA : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left → f z ∉ Active) :
    Nat.card {v : V // f v ∈ Active} =
      Nat.card {e : (geometricGlobalComplementChart Old inner).Carrier //
        f e.1 ∈ Active} := by
  let iOldE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range inner.roots) inner.minimal.1 inner.left
  have hOldA :
      {v : V | f v ∈ Active} =
        iOldE '' {e : (geometricGlobalComplementChart Old inner).Carrier |
          f e.1 ∈ Active} := by
    ext v
    constructor
    · intro hvA
      have hvNotInner : v ∉ functionalComponentFrom Old
          (Set.range inner.roots) inner.left := by
        intro hvInner
        exact hOldInnerNoA v hvInner hvA
      exact ⟨⟨v, hvNotInner⟩, hvA, rfl⟩
    · rintro ⟨e, heA, rfl⟩
      exact heA
  change Nat.card (↑({v : V | f v ∈ Active} : Set V)) =
    Nat.card (↑({e : (geometricGlobalComplementChart Old inner).Carrier |
      f e.1 ∈ Active} : Set
      (geometricGlobalComplementChart Old inner).Carrier))
  simp only [Nat.card_coe_set_eq]
  rw [hOldA]
  exact Set.ncard_image_of_injective _ iOldE.injective

/-- Exact quantitative source cost of the REAL selected-Q
B->A flip when the OLD chosen nonroot component is A-free:

  new total A-active SOURCE support =
  old total A-active SOURCE support +
  NEW Q-nonroot A-active SOURCE support.

The formula does NOT assume that selected Q is A-neutral;
instead it measures the exact cost of its new private vertices.
The removed old component may contain B-exclusive vertices,
which are irrelevant to this A-source accounting identity. -/
theorem geometricSelectedQ_AfreeOld_exact_Aactive_cost
    {V W UT : Type}
    (Old : Structure L V)
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
    (f : V → UT) (flip : W → UT) (Active : Set UT)
    (hOldInnerNoA : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left → f z ∉ Active)
    (hEAgree :
      ∀ e : (geometricGlobalComplementChart Old inner).Carrier,
        flip (iE e) = f e.1) :
    Nat.card {w : W // flip w ∈ Active} =
      Nat.card {v : V // f v ∈ Active} +
      Nat.card {q : Q.Carrier //
        q ∉ Set.range Q.rootEmbedding ∧
        flip (iQ q) ∈ Active} := by
  have hRetained :=
    geometricSelectedQ_Aactive_support_card_add_retained
      Old inner Q New hFiniteNew iQ iE hNewFree
      f flip Active hEAgree
  have hOldCount :=
    geometricSelectedQ_old_Afree_retained_Acard
      Old inner f Active hOldInnerNoA
  simpa only [← hOldCount] using hRetained

end AllThoseRamseyClasses.Lifts
