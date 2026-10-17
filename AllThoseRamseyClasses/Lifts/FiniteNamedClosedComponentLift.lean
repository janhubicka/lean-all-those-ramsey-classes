import AllThoseRamseyClasses.Lifts.FiniteClosedComponentTagLift

/-!
# One finite folded component-tag signature for a finite named forbidden family

A family of FINITELY MANY finite forbidden structures admits a
finite global relation-symbol type if we name ALL authentic
function-closed-root component pieces, not merely the 2019
minimal-separator pieces.

For each named source type there are finitely many closed cuts
and chosen complementary Gaifman components. The dependent sum
of these tag types over a finite index of source representatives
is finite. The canonical folded expansion records the WEAK EHN
realization of each actual tagged native component piece on a
possibly repeated root-image tuple.

This gives a literal finite-signature auxiliary lift for a
finite collection of named source structures, with exact old
relations and entire original partial-function interpretations.
It has finitely many expansions over every finite OLD shadow.

The major remaining bridge is to transport forbidden source
witnesses along ISOMORPHISMS to the chosen finite representatives
and use the canonical predicates to retarget any A-only component
across a common FULL expanded witness. This module does not
claim strong amalgamation, ordering, Ramsey, or the theorem for
general regular infinite forbidden families.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- A finite list of finite named forbidden functional sources.
The component-indexed auxiliary expansion can be constructed
using ONLY these representatives. Isomorphism closure of an
external forbidden predicate is handled separately. -/
structure FiniteNamedFunctionalSources (L : Language.{u}) where
  Index : Type v
  finiteIndex : Finite Index
  Carrier : Index → Type v
  finiteCarrier : ∀ i, Finite (Carrier i)
  source : ∀ i, Structure L (Carrier i)

/-- One authentic closed-root component from one source in the
finite named family. Each entry is literally a pair:
source index, actual closed-root component tag. -/
abbrev FiniteNamedFunctionalSources.ComponentTag
    (Family : FiniteNamedFunctionalSources.{u,v} L) :=
  Σ i : Family.Index, ClosedComponentTag (Family.source i)

/-- The TOTAL collection of tagged component symbols is finite,
not merely the collection at each fixed arity. This is the key
finite-forbidden-family advantage over regular infinite families. -/
theorem finiteNamedComponentTag_finite
    (Family : FiniteNamedFunctionalSources.{u,v} L) :
    Finite Family.ComponentTag := by
  letI : Finite Family.Index := Family.finiteIndex
  letI (i : Family.Index) : Finite (Family.Carrier i) :=
    Family.finiteCarrier i
  letI (i : Family.Index) :
      Finite (ClosedComponentTag (Family.source i)) :=
    closedComponentTag_finite (Family.source i)
  infer_instance

noncomputable instance
    (Family : FiniteNamedFunctionalSources.{u,v} L) :
    Finite Family.ComponentTag :=
  finiteNamedComponentTag_finite Family

/-- Arity of the full closed-root tuple of a named source piece. -/
noncomputable def FiniteNamedFunctionalSources.ComponentTag.width
    (Family : FiniteNamedFunctionalSources.{u,v} L)
    (tag : Family.ComponentTag) : ℕ :=
  tag.2.width

/-- Actual full functional rooted pattern of one named source
component, not merely a candidate rooted relational graph.
The complete root is enumerated without source repetitions. -/
noncomputable def FiniteNamedFunctionalSources.ComponentTag.pattern
    (Family : FiniteNamedFunctionalSources.{u,v} L)
    (tag : Family.ComponentTag) :
    FunctionalRootedPattern L (tag.width Family) := by
  rcases tag with ⟨i, t⟩
  letI : Finite (Family.Carrier i) :=
    Family.finiteCarrier i
  exact t.rootedPattern

/-- The alternative finite-index folded canonical expansion of
a finite named forbidden family, with an added relation symbol
for EVERY authentic arbitrary CLOSED-root component pattern.
Root-image collisions are explicitly allowed. -/
noncomputable def finiteNamedClosedComponentFoldedLift
    (Family : FiniteNamedFunctionalSources.{u,v} L)
    {W : Type v} (A : Structure L W) :
    Structure
      (functionalLiftLanguageBig L
        Family.ComponentTag
        (fun tag => tag.width Family)) W :=
  functionalWithExtraBig L
    Family.ComponentTag
    (fun tag => tag.width Family) A
    (fun tag xs =>
      FunctionalRootRealization (tag.pattern Family) A xs)

/-- Every original relation and function interpretation is
preserved exactly by the finite named-family folded lift. -/
@[simp] theorem finiteNamedClosedComponentFoldedLift_shadow
    (Family : FiniteNamedFunctionalSources.{u,v} L)
    {W : Type v} (A : Structure L W) :
    functionalShadowBig L Family.ComponentTag
      (fun tag => tag.width Family)
      (finiteNamedClosedComponentFoldedLift Family A) = A :=
  functionalShadowBig_withExtra
    L Family.ComponentTag (fun tag => tag.width Family) A _

/-- Relation membership is EXACTLY the realization of the
specific true named closed-root component piece. -/
theorem finiteNamedClosedComponentFoldedLift_relation_iff
    (Family : FiniteNamedFunctionalSources.{u,v} L)
    {W : Type v} (A : Structure L W)
    (tag : Family.ComponentTag)
    (xs : Fin (tag.width Family) → W) :
    (finiteNamedClosedComponentFoldedLift Family A).rel
      (.inr tag) xs ↔
    FunctionalRootRealization (tag.pattern Family) A xs := by
  rfl

/-- For every finite old native functional shadow, there are
finitely many expanded structures in the finite named-family
component-tag language. No OLD-language symbol finiteness
and no injectivity of root-image tuples are assumed. -/
theorem finiteNamedClosedComponentFoldedLift_finiteShadowFibre
    (Family : FiniteNamedFunctionalSources.{u,v} L)
    {W : Type v} [Finite W] (A : Structure L W) :
    Finite (FixedFunctionalShadowExpansions L
      Family.ComponentTag
      (fun tag => tag.width Family) A) :=
  fixedFunctionalShadowExpansions_finite
    L Family.ComponentTag (fun tag => tag.width Family) A

end AllThoseRamseyClasses.Lifts
