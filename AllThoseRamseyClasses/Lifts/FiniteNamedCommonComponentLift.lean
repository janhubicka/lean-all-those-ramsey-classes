import AllThoseRamseyClasses.Lifts.FiniteNamedClosedComponentLift

/-!
# One common FULL tagged lift transfers every named forbidden-component realization

A finite named family of finite native functional sources carries ONE
finite collection of relation symbols, indexed by a source identifier
and one ACTUAL arbitrary function-closed-root component piece.

If the canonical folded lifts of Left and Right induce the SAME
full expanded structure on the common old-language root X, then all
these named relation predicates agree on every ordered X tuple.
In particular every weak rooted realization of any actual component
of ANY source in the named family in Left transfers to a weak
realization of the SAME full functional component in Right,
even with colliding root images.

This is exactly the semantic transfer input for the direct
source-preserving component fold. The statement is conditional on
the given shared FULL expanded structure; existence of maximal
witnesses and strong amalgamation of the lifted class are separate.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Full agreement of every single combined finite-family
closed-root component symbol on the common old root X. -/
def FiniteNamedComponentLiftsAgreeOn
    (Family : FiniteNamedFunctionalSources.{u,v} L)
    {UX UA UB : Type v}
    {X : Structure L UX}
    {A : Structure L UA}
    {B : Structure L UB}
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B) : Prop :=
  ∀ (tag : Family.ComponentTag)
    (xs : Fin (tag.width Family) → UX),
    (finiteNamedClosedComponentFoldedLift Family A).rel
      (.inr tag) (iA ∘ xs) ↔
    (finiteNamedClosedComponentFoldedLift Family B).rel
      (.inr tag) (iB ∘ xs)

/-- A single shared FULL expansion of the common old-language
root X in the finite COMBINED tag language, together with full
embeddings into the canonical lifts of both ambient witnesses. -/
structure CommonFiniteNamedComponentLift
    (Family : FiniteNamedFunctionalSources.{u,v} L)
    {UX UA UB : Type v}
    (X : Structure L UX)
    (A : Structure L UA)
    (B : Structure L UB)
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B) where
  lifted : Structure
    (functionalLiftLanguageBig L Family.ComponentTag
      (fun tag => tag.width Family)) UX
  shadow_eq :
    functionalShadowBig L Family.ComponentTag
      (fun tag => tag.width Family) lifted = X
  intoA : Structure.Embedding lifted
    (finiteNamedClosedComponentFoldedLift Family A)
  intoB : Structure.Embedding lifted
    (finiteNamedClosedComponentFoldedLift Family B)
  intoA_verts : ∀ x : UX, intoA x = iA x
  intoB_verts : ∀ x : UX, intoB x = iB x

/-- Relation agreement follows by reflection of the very same
tag symbol through the two full embeddings of the shared
lifted root X. Applies to repeated-coordinate root tuples. -/
theorem CommonFiniteNamedComponentLift.agreeOn
    (Family : FiniteNamedFunctionalSources.{u,v} L)
    {UX UA UB : Type v}
    {X : Structure L UX}
    {A : Structure L UA}
    {B : Structure L UB}
    {iA : Structure.Embedding X A}
    {iB : Structure.Embedding X B}
    (h : CommonFiniteNamedComponentLift
      Family X A B iA iB) :
    FiniteNamedComponentLiftsAgreeOn Family iA iB := by
  intro tag xs
  have hA :
      h.intoA.toFun ∘ xs = iA.toFun ∘ xs := by
    funext k
    exact h.intoA_verts (xs k)
  have hB :
      h.intoB.toFun ∘ xs = iB.toFun ∘ xs := by
    funext k
    exact h.intoB_verts (xs k)
  calc
    (finiteNamedClosedComponentFoldedLift Family A).rel
        (.inr tag) (iA ∘ xs)
        ↔ (finiteNamedClosedComponentFoldedLift Family A).rel
            (.inr tag) (h.intoA ∘ xs) := by
          exact Iff.of_eq (congrArg
            (fun q : Fin (tag.width Family) → UA =>
              (finiteNamedClosedComponentFoldedLift Family A).rel
                (.inr tag) q) hA.symm)
    _ ↔ h.lifted.rel (.inr tag) xs :=
      h.intoA.map_rel_iff (.inr tag) xs
    _ ↔ (finiteNamedClosedComponentFoldedLift Family B).rel
        (.inr tag) (h.intoB ∘ xs) :=
      (h.intoB.map_rel_iff (.inr tag) xs).symm
    _ ↔ (finiteNamedClosedComponentFoldedLift Family B).rel
        (.inr tag) (iB ∘ xs) := by
          exact Iff.of_eq (congrArg
            (fun q : Fin (tag.width Family) → UB =>
              (finiteNamedClosedComponentFoldedLift Family B).rel
                (.inr tag) q) hB)

/-- The common full combined family lift transfers a WEAK
realization of one exact native closed-root component piece
of the ith forbidden source into Right on the matching X
root tuple. No root-image injectivity or source quotient. -/
theorem commonFiniteNamedComponentLift_rightWitness
    (Family : FiniteNamedFunctionalSources.{u,v} L)
    {UX UA UB : Type v}
    (X : Structure L UX)
    (A : Structure L UA)
    (B : Structure L UB)
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B)
    (hCommon : CommonFiniteNamedComponentLift
      Family X A B iA iB)
    (i : Family.Index)
    (tag : ClosedComponentTag (Family.source i))
    (xs : Fin tag.width → UX)
    (hLeft : FunctionalRootRealization tag.rootedPattern
      A (iA ∘ xs)) :
    FunctionalRootRealization tag.rootedPattern
      B (iB ∘ xs) := by
  let T : Family.ComponentTag := ⟨i, tag⟩
  have hRelLeft :
      (finiteNamedClosedComponentFoldedLift Family A).rel
        (.inr T) (iA ∘ xs) := by
    change FunctionalRootRealization tag.rootedPattern
      A (iA ∘ xs)
    exact hLeft
  have hRelRight :
      (finiteNamedClosedComponentFoldedLift Family B).rel
        (.inr T) (iB ∘ xs) :=
    (hCommon.agreeOn Family T xs).mp hRelLeft
  change FunctionalRootRealization tag.rootedPattern
    B (iB ∘ xs) at hRelRight
  exact hRelRight

end AllThoseRamseyClasses.Lifts
