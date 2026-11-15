import AllThoseRamseyClasses.Lifts.Claim2SelectedQAactiveSourceCost

/-!
# Preservation of global A-minimality iff private Q-nonroots are A-free

For an ORIGINAL globally A-source-support-minimal forbidden
native weak EHN witness, a genuine selected-Q full replacement
of an OLD A-free chosen component has an EXACT numerical cost:

  new total A-support =
    old total A-support + NEW Q-private A-support.

The new source/weak-map witness is globally minimum for total
A-source support among the same forbidden family and fixed full
target IF AND ONLY IF that additional private-Q A-support is zero.
Equivalently, EVERY genuinely inserted Q nonroot SOURCE vertex
maps outside the A-exclusive target region.

The forward direction is important: if one Q-nonroot maps to
A-exclusive target, the old forbidden map itself is a valid
candidate of strictly smaller total A-support, so the new
witness cannot still be globally minimal. No inference about
weak map injectivity is used.

This is a theorem about a SPECIFIC actual chosen replacement Q,
not an existence theorem for an A-neutral Q. In particular, it
does not validate the currently missing unrestricted 2019
Claim 2 B-descent induction.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Given an original globally minimum A-active SOURCE witness,
the new forbidden witness obtained by a genuine selected-Q full
native source flip is ALSO globally minimum exactly when EVERY
inserted Q-nonroot SOURCE vertex is A-INACTIVE.

Only source cardinality and full native source embeddings are
used; there is no distinct-target-image quotient. -/
theorem geometricSelectedQ_globalAMinimum_iff_nonrootAfree
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {V W UT : Type}
    (Old : Structure L V) (hOld : F Old)
    {m : ℕ}
    (inner : GeometricFunctionalPieceData Old m)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (New : Structure L W) (hNew : F New)
    (hFiniteNew : Finite W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (Target : Structure L UT)
    (f : V → UT) (hf : Old.IsEHNHomomorphismEmbedding Target f)
    (flip : W → UT) (hFlip : New.IsEHNHomomorphismEmbedding Target flip)
    (Active : Set UT)
    (hOldInnerNoA : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left → f z ∉ Active)
    (hEAgree :
      ∀ e : (geometricGlobalComplementChart Old inner).Carrier,
        flip (iE e) = f e.1)
    (hOldGlobalMin : ∀ {Z : Type}
      (Candidate : Structure L Z) (hCandidate : F Candidate)
      (g : Z → UT),
      Candidate.IsEHNHomomorphismEmbedding Target g →
      Nat.card {v : V // f v ∈ Active} ≤
        Nat.card {z : Z // g z ∈ Active}) :
    (∀ {Z : Type}
      (Candidate : Structure L Z) (hCandidate : F Candidate)
      (g : Z → UT),
      Candidate.IsEHNHomomorphismEmbedding Target g →
      Nat.card {w : W // flip w ∈ Active} ≤
        Nat.card {z : Z // g z ∈ Active})
    ↔
    (∀ q : Q.Carrier,
      q ∉ Set.range Q.rootEmbedding →
        flip (iQ q) ∉ Active) := by
  classical
  have hCost :
      Nat.card {w : W // flip w ∈ Active} =
        Nat.card {v : V // f v ∈ Active} +
        Nat.card {q : Q.Carrier //
          q ∉ Set.range Q.rootEmbedding ∧
          flip (iQ q) ∈ Active} :=
    geometricSelectedQ_AfreeOld_exact_Aactive_cost
      Old inner Q New hFiniteNew iQ iE hNewFree
      f flip Active hOldInnerNoA hEAgree
  constructor
  · intro hNewMin q hNonroot hqA
    letI : Finite Q.Carrier :=
      Finite.of_injective (fun q : Q.Carrier => iQ q) iQ.injective
    letI : Fintype Q.Carrier := Fintype.ofFinite Q.Carrier
    have hPrivateNonempty :
        Nonempty {q : Q.Carrier //
          q ∉ Set.range Q.rootEmbedding ∧
          flip (iQ q) ∈ Active} :=
      ⟨⟨q, hNonroot, hqA⟩⟩
    have hPrivatePositive :
        0 < Nat.card {q : Q.Carrier //
          q ∉ Set.range Q.rootEmbedding ∧
          flip (iQ q) ∈ Active} := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr hPrivateNonempty
    have hOldStrictlySmaller :
        Nat.card {v : V // f v ∈ Active} <
          Nat.card {w : W // flip w ∈ Active} := by
      rw [hCost]
      exact Nat.lt_add_of_pos_right hPrivatePositive
    exact (Nat.not_lt_of_ge (hNewMin Old hOld f hf))
      hOldStrictlySmaller
  · intro hAllQNonrootAfree
    have hPrivateEmpty :
        ({q : Q.Carrier |
          q ∉ Set.range Q.rootEmbedding ∧
          flip (iQ q) ∈ Active} : Set Q.Carrier) = ∅ := by
      ext q
      constructor
      · intro h
        exact (hAllQNonrootAfree q h.1) h.2
      · intro h
        simp at h
    have hPrivateZero :
        Nat.card {q : Q.Carrier //
          q ∉ Set.range Q.rootEmbedding ∧
          flip (iQ q) ∈ Active} = 0 := by
      change Nat.card (↑({q : Q.Carrier |
        q ∉ Set.range Q.rootEmbedding ∧
        flip (iQ q) ∈ Active} : Set Q.Carrier)) = 0
      rw [Nat.card_coe_set_eq, hPrivateEmpty]
      simp
    have hEqual :
        Nat.card {w : W // flip w ∈ Active} =
          Nat.card {v : V // f v ∈ Active} := by
      simpa only [hPrivateZero, Nat.add_zero] using hCost
    intro Z Candidate hCandidate g hg
    calc
      Nat.card {w : W // flip w ∈ Active} =
          Nat.card {v : V // f v ∈ Active} := hEqual
      _ ≤ Nat.card {z : Z // g z ∈ Active} :=
        hOldGlobalMin Candidate hCandidate g hg

end AllThoseRamseyClasses.Lifts
