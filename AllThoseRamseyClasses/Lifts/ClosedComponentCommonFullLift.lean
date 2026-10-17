import AllThoseRamseyClasses.Lifts.FiniteClosedComponentTagLift

/-!
# Agreement of ALL genuine closed-component predicates on a shared full lift

For one named finite forbidden source Source, the auxiliary full
closed-component tag lift has a FINITE new relation-symbol type.
Each tag records weak EHN realization of its actual native
function-closed-root component piece (with folded root images).

If two ambient witnesses A and B induce exactly the SAME full
tagged lifted substructure on the shared old root X, the extra
component predicates agree on every ordered tuple of X.

This module packages the precise common-full-lift witness
and proves relation transfer, including tuples with repeated
target root coordinates. The old relation/function shadow and
all full functional embeddings are retained exactly.

Existence of maximal common tagged witnesses and the general
strong-amalgamation theorem are separate tasks. Merely sharing
an OLD-language substructure does not provide this relation
agreement; the expanded FULL embeddings are essential.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Every authentic closed-root component predicate agrees on
the common root X when evaluated on its corresponding images
in the two canonical tagged lifts. -/
def AllClosedComponentLiftsAgreeOn
    [Finite V]
    (Source : Structure L V)
    {UX UA UB : Type v}
    {X : Structure L UX}
    {A : Structure L UA} {B : Structure L UB}
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B) : Prop :=
  ∀ (tag : ClosedComponentTag Source)
    (xs : Fin tag.width → UX),
    (allClosedComponentFoldedLift Source A).rel
      (.inr tag) (iA ∘ xs) ↔
    (allClosedComponentFoldedLift Source B).rel
      (.inr tag) (iB ∘ xs)

/-- One COMMON FULL tagged lifted structure inducing X as its
literal old functional shadow, with two prescribed expanded
full embeddings into the canonical tagged lifts of A and B. -/
structure CommonAllClosedComponentLift
    [Finite V]
    (Source : Structure L V)
    {UX UA UB : Type v}
    (X : Structure L UX)
    (A : Structure L UA)
    (B : Structure L UB)
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B) where
  lifted : Structure
    (functionalLiftLanguageBig L
      (ClosedComponentTag Source)
      (fun t => t.width)) UX
  shadow_eq :
    functionalShadowBig L (ClosedComponentTag Source)
      (fun t => t.width) lifted = X
  intoA : Structure.Embedding lifted
    (allClosedComponentFoldedLift Source A)
  intoB : Structure.Embedding lifted
    (allClosedComponentFoldedLift Source B)
  intoA_verts : ∀ x : UX, intoA x = iA x
  intoB_verts : ∀ x : UX, intoB x = iB x

/-- Full induced expanded embeddings force equality of ALL
tagged native component-piece relations, even if root-image
coordinates collide. No arbitrary OLD embedding reflection
of canonical predicates is asserted. -/
theorem CommonAllClosedComponentLift.agreeOn
    [Finite V]
    (Source : Structure L V)
    {UX UA UB : Type v}
    {X : Structure L UX}
    {A : Structure L UA} {B : Structure L UB}
    {iA : Structure.Embedding X A}
    {iB : Structure.Embedding X B}
    (h : CommonAllClosedComponentLift Source X A B iA iB) :
    AllClosedComponentLiftsAgreeOn Source iA iB := by
  intro t xs
  have hA :
      h.intoA.toFun ∘ xs = iA.toFun ∘ xs := by
    funext k
    exact h.intoA_verts (xs k)
  have hB :
      h.intoB.toFun ∘ xs = iB.toFun ∘ xs := by
    funext k
    exact h.intoB_verts (xs k)
  calc
    (allClosedComponentFoldedLift Source A).rel (.inr t) (iA ∘ xs)
        ↔ (allClosedComponentFoldedLift Source A).rel (.inr t)
            (h.intoA ∘ xs) := by
          exact Iff.of_eq (congrArg
            (fun q : Fin t.width → UA =>
              (allClosedComponentFoldedLift Source A).rel (.inr t) q)
            hA.symm)
    _ ↔ h.lifted.rel (.inr t) xs :=
      h.intoA.map_rel_iff (.inr t) xs
    _ ↔ (allClosedComponentFoldedLift Source B).rel (.inr t)
        (h.intoB ∘ xs) :=
      (h.intoB.map_rel_iff (.inr t) xs).symm
    _ ↔ (allClosedComponentFoldedLift Source B).rel (.inr t)
        (iB ∘ xs) := by
          exact Iff.of_eq (congrArg
            (fun q : Fin t.width → UB =>
              (allClosedComponentFoldedLift Source B).rel (.inr t) q)
            hB)

/-- Restrict a FULL embedding into the finite-source tagged lift
to a FULL embedding of the exact original functional shadow. -/
def allClosedComponentLift_shadowEmbedding
    [Finite V]
    (Source : Structure L V)
    {UX UA : Type v}
    (LiftX : Structure
      (functionalLiftLanguageBig L
        (ClosedComponentTag Source)
        (fun t => t.width)) UX)
    (A : Structure L UA)
    (e : Structure.Embedding LiftX
      (allClosedComponentFoldedLift Source A)) :
    Structure.Embedding
      (functionalShadowBig L
        (ClosedComponentTag Source)
        (fun t => t.width) LiftX)
      A := by
  have h : Structure.Embedding
      (functionalShadowBig L (ClosedComponentTag Source)
        (fun t => t.width) LiftX)
      (functionalShadowBig L (ClosedComponentTag Source)
        (fun t => t.width)
        (allClosedComponentFoldedLift Source A)) :=
    functionalShadowBigEmbedding L
      (ClosedComponentTag Source)
      (fun t => t.width) e
  simpa only [allClosedComponentFoldedLift_shadow] using h

/-- The shadow map is the same function on EVERY original
vertex, not just the chosen root coordinates. -/
theorem allClosedComponentLift_shadowEmbedding_apply
    [Finite V]
    (Source : Structure L V)
    {UX UA : Type v}
    (LiftX : Structure
      (functionalLiftLanguageBig L
        (ClosedComponentTag Source)
        (fun t => t.width)) UX)
    (A : Structure L UA)
    (e : Structure.Embedding LiftX
      (allClosedComponentFoldedLift Source A))
    (x : UX) :
    allClosedComponentLift_shadowEmbedding Source LiftX A e x =
      e x := by
  rfl

/-- Two full embeddings of the SAME tagged expansion of X
automatically give every field of the common lifted witness.
No redundant root-agreement oracle is needed once that shared
induced expansion has actually been supplied. -/
def commonAllClosedComponentLift_of_sharedExpansion
    [Finite V]
    (Source : Structure L V)
    {UX UA UB : Type v}
    (LiftX : Structure
      (functionalLiftLanguageBig L
        (ClosedComponentTag Source)
        (fun t => t.width)) UX)
    (A : Structure L UA)
    (B : Structure L UB)
    (eA : Structure.Embedding LiftX
      (allClosedComponentFoldedLift Source A))
    (eB : Structure.Embedding LiftX
      (allClosedComponentFoldedLift Source B)) :
    CommonAllClosedComponentLift Source
      (functionalShadowBig L (ClosedComponentTag Source)
        (fun t => t.width) LiftX)
      A B
      (allClosedComponentLift_shadowEmbedding Source LiftX A eA)
      (allClosedComponentLift_shadowEmbedding Source LiftX B eB) where
  lifted := LiftX
  shadow_eq := rfl
  intoA := eA
  intoB := eB
  intoA_verts := fun x =>
    (allClosedComponentLift_shadowEmbedding_apply
      Source LiftX A eA x).symm
  intoB_verts := fun x =>
    (allClosedComponentLift_shadowEmbedding_apply
      Source LiftX B eB x).symm

end AllThoseRamseyClasses.Lifts
