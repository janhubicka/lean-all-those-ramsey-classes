import PartiteConstruction.Structure.FreeAmalgam

/-!
# Finite exclusive-support bounds under surjective image reductions

The strong-amalgamation proof of Hubička--Nešetřil (2019) first
selects an injectively embedded forbidden source with the minimum
number of vertices mapped to one exclusive amalgamation side.

A flip can produce a NEW weak map that is no longer injective.
The paper then invokes closure of its forbidden family under
tuple-surjective homomorphism-embedding images to recover an
injectively embedded forbidden source. The crucial FINITE
cardinality step is independent of how that image is constructed.

If a weakly mapped new source surjects onto a quotient source,
and the target map factors through this quotient, the number
of quotient vertices mapping to the A-only set cannot exceed the
number of original vertices mapping there. Combined with the
strict support decrease under a successful flip, this gives the
numerical contradiction required by the minimality argument.

WARNING: this lemma is solely the cardinality consequence of
a surjective vertex quotient. It does NOT assert existence of
a forbidden quotient, tuple-surjectivity on defined partial
function domains, or a full embedding of the quotient source
into the original ambient free amalgam. Those are separate
image-closure hypotheses/proof obligations.
-/

namespace AllThoseRamseyClasses.Lifts

universe u v w

/-- Under a surjective vertex quotient, the cardinality of the
A-only support of the quotient map is at most the cardinality
of the A-only support of the original map. -/
theorem exclusiveSupport_card_le_of_surjective
    {Source : Type u} {Quotient : Type v} {Target : Type w}
    [Finite Source] [Finite Quotient]
    (q : Source → Quotient) (hq : Function.Surjective q)
    (p : Quotient → Target) (AOnly : Set Target) :
    Nat.card {y : Quotient // p y ∈ AOnly} ≤
      Nat.card {x : Source // p (q x) ∈ AOnly} := by
  classical
  letI : Fintype Source := Fintype.ofFinite Source
  letI : Fintype Quotient := Fintype.ofFinite Quotient
  let supportQuotient :
      {x : Source // p (q x) ∈ AOnly} →
      {y : Quotient // p y ∈ AOnly} :=
    fun x => ⟨q x.1, x.2⟩
  have hSurj : Function.Surjective supportQuotient := by
    intro y
    obtain ⟨x, hx⟩ := hq y.1
    refine ⟨⟨x, ?_⟩, ?_⟩
    · simpa only [hx] using y.2
    · apply Subtype.ext
      exact hx
  have hCard :
      Fintype.card {y : Quotient // p y ∈ AOnly} ≤
        Fintype.card {x : Source // p (q x) ∈ AOnly} :=
    Fintype.card_le_of_surjective supportQuotient hSurj
  simpa only [Nat.card_eq_fintype_card] using hCard

/-- The weak-map factorization can be supplied by an arbitrary
image-reduction argument: support cannot increase on its
surjective image, even when the old map has collisions. -/
theorem exclusiveSupport_card_le_of_factorization
    {Source : Type u} {Quotient : Type v} {Target : Type w}
    [Finite Source] [Finite Quotient]
    (q : Source → Quotient) (hq : Function.Surjective q)
    (pSource : Source → Target) (pQuotient : Quotient → Target)
    (hFactor : ∀ x, pSource x = pQuotient (q x))
    (AOnly : Set Target) :
    Nat.card {y : Quotient // pQuotient y ∈ AOnly} ≤
      Nat.card {x : Source // pSource x ∈ AOnly} := by
  have heq : pSource = pQuotient ∘ q := by
    funext x
    exact hFactor x
  subst pSource
  exact exclusiveSupport_card_le_of_surjective q hq pQuotient AOnly

/-- Applying a surjective image reduction AFTER a successful
strict-support-decreasing flip preserves the strict inequality
against the ORIGINAL forbidden source. This is the exact
finite comparison used in the published minimality argument,
once its independent forbidden-image existence conditions hold. -/
theorem exclusiveSupport_strict_decrease_after_quotient
    {OldSource : Type u} {NewSource : Type v}
    {Quotient : Type w} {Target : Type*}
    [Finite OldSource] [Finite NewSource] [Finite Quotient]
    (pOld : OldSource → Target)
    (pNew : NewSource → Target)
    (pQuotient : Quotient → Target)
    (q : NewSource → Quotient)
    (hq : Function.Surjective q)
    (hFactor : ∀ x, pNew x = pQuotient (q x))
    (AOnly : Set Target)
    (hFlipDecrease :
      Nat.card {x : NewSource // pNew x ∈ AOnly} <
        Nat.card {x : OldSource // pOld x ∈ AOnly}) :
    Nat.card {y : Quotient // pQuotient y ∈ AOnly} <
      Nat.card {x : OldSource // pOld x ∈ AOnly} := by
  exact lt_of_le_of_lt
    (exclusiveSupport_card_le_of_factorization
      q hq pNew pQuotient hFactor AOnly)
    hFlipDecrease

end AllThoseRamseyClasses.Lifts
