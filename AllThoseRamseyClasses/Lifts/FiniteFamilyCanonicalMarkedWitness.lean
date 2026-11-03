import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceAge
import PartiteConstruction.Structure.Order

/-!
# Track E: extract the actual marked B-copy from its native witness

A finite maximal induced trace B* is presented by a full native
embedding i : shadow(B*) -> W into a finite forbidden-free witness.
By its membership condition, the NEW folded component relations of
B* are exactly the relations of the canonical folded lift of W
observed on the embedded root.

Therefore that same native embedding lifts to a FULL expanded
embedding B* -> foldedLift(W), reflecting all original complete
partial/set-valued function fibres AND all added tag relations.
No native witness maximality is needed for this particular
embedding beyond the equality of observed tag profiles.

With a chosen linear order on W making i strictly increasing,
the embedding becomes a FULL ordered embedding into foldedLift(W)
with that order. The separate finite-injection order-extension
lemma supplies such an order; no order is assumed automatically
from a native full embedding.

This is the exact marked-copy data used by the certified
finiteNamedMarkedWitnessRamsey_of_nativeAvoidance endgame. It
is independent of local Ramsey-picture sparsening, and does not
prove the finite-family Ramsey theorem alone.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Any finite-family trace whose new relations reflect a native
witness W embeds FULLY into W's ACTUAL canonical folded lift.

The old relation reflection and complete set-valued function
fibre reflection come directly from the native embedding iW.
The added relation reflection is precisely the trace's recorded
profile equivalence hRel, including repeated root coordinates. -/
noncomputable def finiteNamedMaximalTrace_into_foldedWitness
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VB VW : Type}
    (B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB)
    (W : Structure L VW)
    (iW : Structure.Embedding (FiniteNamedTraceShadow Family B) W)
    (hRel : ∀ (tag : Family.ComponentTag)
      (xs : Fin (tag.width Family) → VB),
      B.rel (.inr tag) xs ↔
        (finiteNamedClosedComponentFoldedLift Family W).rel
          (.inr tag) (iW ∘ xs)) :
    Structure.Embedding B (finiteNamedClosedComponentFoldedLift Family W) where
  toFun := iW
  injective := iW.injective
  map_rel_iff := by
    intro R xs
    cases R with
    | inl R =>
        change W.rel R.down (iW ∘ xs) ↔
          (FiniteNamedTraceShadow Family B).rel R.down xs
        exact iW.map_rel_iff R.down xs
    | inr tag =>
        exact (hRel tag xs).symm
  map_func := by
    intro F xs
    change imageSet iW
      ((FiniteNamedTraceShadow Family B).func F.down xs) =
      W.func F.down (iW ∘ xs)
    exact iW.map_func F.down xs

/-- If the prescribed finite native witness is given a linear
order compatible with iW, the canonical marked trace inclusion
is a FULL ordered embedding. Every old native set-valued
function fibre and new folded predicate is reflected. -/
noncomputable def finiteNamedMaximalTrace_into_foldedWitness_ordered
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VB VW : Type} [LinearOrder VB] [LinearOrder VW]
    (B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB)
    (W : Structure L VW)
    (iW : Structure.Embedding (FiniteNamedTraceShadow Family B) W)
    (hRel : ∀ (tag : Family.ComponentTag)
      (xs : Fin (tag.width Family) → VB),
      B.rel (.inr tag) xs ↔
        (finiteNamedClosedComponentFoldedLift Family W).rel
          (.inr tag) (iW ∘ xs))
    (hMono : StrictMono iW) :
    Structure.Embedding B.withLinearOrder
      (finiteNamedClosedComponentFoldedLift Family W).withLinearOrder := by
  let j : Structure.Embedding B
      (finiteNamedClosedComponentFoldedLift Family W) :=
    finiteNamedMaximalTrace_into_foldedWitness
      Family B W iW hRel
  exact {
    toFun := j
    injective := j.injective
    map_rel_iff := by
      intro R xs
      cases R with
      | inl R => exact j.map_rel_iff R xs
      | inr _ => exact hMono.lt_iff_lt
    map_func := j.map_func
  }

end AllThoseRamseyClasses.Lifts
