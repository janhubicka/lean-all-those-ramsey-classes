import AllThoseRamseyClasses.Lifts.FiniteClosedSeparatorSelection
import PartiteConstruction.Functional.WeakInvariant
import Mathlib.Data.Set.Card

/-!
# Minimal source support for possibly NONINJECTIVE forbidden HE witnesses

The Section 3 proof of strong amalgamation chooses a forbidden
homomorphism-embedding f:F -> D minimizing the number of source
vertices mapped into the A-only part of a free amalgam.

It is NOT necessary to injectivize f before making this choice.
In fact, the published blanket image-closure injectivization
shortcut is invalid without extra assumptions. A nonempty family
of actual weak EHN forbidden witnesses admits a minimizer of the
natural number support count by well ordering of the naturals.

This module packages the real source witness and exact source
support count, proves the minimum exists even when carrier types
and source structures vary between candidates, and supplies a
generic strict-descent contradiction. No main-theorem conclusion,
maximal-lift existence, source-closure repair or geometric flip
is hidden in the assumptions.

The users of this result must later construct a strict-descent
witness under the original theorem hypotheses; the conditional
folded-root/one-component flip already supplies such a step in
its restricted setting.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- One actual forbidden-source weak homomorphism-embedding into
a fixed target, with no injectivity or replacement quotient. -/
structure ForbiddenEHNWitness
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UT : Type} (Target : Structure L UT) where
  Carrier : Type
  source : Structure L Carrier
  forbidden : F source
  toTarget : Carrier → UT
  homEmbedding : source.IsEHNHomomorphismEmbedding Target toTarget

/-- The exact natural-number measure on SOURCE vertices whose
images belong to a specified subset of the target. -/
def ForbiddenEHNWitness.sourceSupportCount
    {F : ∀ {W : Type}, Structure L W → Prop}
    {UT : Type} {Target : Structure L UT}
    (w : ForbiddenEHNWitness F Target)
    (AOnly : Set UT) : ℕ :=
  Nat.card {v : w.Carrier // w.toTarget v ∈ AOnly}

/-- A minimizer exists among all actual forbidden weak EHN maps
to the fixed target, even though the source carriers and full
functional structures may vary between witnesses. -/
theorem exists_minimalForbiddenEHNWitness_support
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ w : ForbiddenEHNWitness F Target,
      ∀ v : ForbiddenEHNWitness F Target,
        w.sourceSupportCount AOnly ≤ v.sourceSupportCount AOnly := by
  classical
  let sizes : Set ℕ :=
    {n | ∃ w : ForbiddenEHNWitness F Target,
      w.sourceSupportCount AOnly = n}
  have hNonempty : sizes.Nonempty := by
    obtain ⟨w⟩ := hExists
    exact ⟨w.sourceSupportCount AOnly, w, rfl⟩
  have hMin : sInf sizes ∈ sizes := Nat.sInf_mem hNonempty
  obtain ⟨w, hCard⟩ := hMin
  refine ⟨w, ?_⟩
  intro v
  rw [hCard]
  exact Nat.sInf_le (show v.sourceSupportCount AOnly ∈ sizes from
    ⟨v, rfl⟩)

/-- A chosen support minimizer cannot have ANY actual forbidden
weak EHN replacement of strictly smaller source support. -/
theorem minimalForbiddenEHNWitness_no_strict_drop
    {F : ∀ {W : Type}, Structure L W → Prop}
    {UT : Type} {Target : Structure L UT}
    (AOnly : Set UT)
    (w : ForbiddenEHNWitness F Target)
    (hMinimal : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount AOnly ≤ v.sourceSupportCount AOnly)
    (v : ForbiddenEHNWitness F Target) :
    ¬ v.sourceSupportCount AOnly < w.sourceSupportCount AOnly :=
  Nat.not_lt_of_ge (hMinimal v)

/-- The core contradiction mechanism for the Section 3 minimality
proof. If every actual bad source map to the target can be
replaced by another forbidden HE map strictly decreasing its
source A-only support, then there is NO forbidden weak HE map
to the target.

This theorem does NOT assert the required descent step, which is
precisely the still-open general Claim 1/2 geometric construction. -/
theorem noForbiddenEHNWitness_of_strictSupportDescent
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (hDescent : ∀ w : ForbiddenEHNWitness F Target,
      ∃ v : ForbiddenEHNWitness F Target,
        v.sourceSupportCount AOnly < w.sourceSupportCount AOnly) :
    ¬ Nonempty (ForbiddenEHNWitness F Target) := by
  intro hExists
  obtain ⟨w, hw⟩ :=
    exists_minimalForbiddenEHNWitness_support
      F Target AOnly hExists
  obtain ⟨v, hlt⟩ := hDescent w
  exact (minimalForbiddenEHNWitness_no_strict_drop
    AOnly w hw v) hlt

end AllThoseRamseyClasses.Lifts
