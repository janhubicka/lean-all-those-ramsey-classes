import AllThoseRamseyClasses.Lifts.Claim2IteratedContextualDescent

/-!
# Claim 2: a single transported outer context, with its local support rank

The component proofs in the native functional library must apply to
THE SAME actual inner replacement, not to unrelated witnesses
chosen by two existential lemmas.

This package accepts ONE old/new full functional source diagram,
ONE old/new target-map pair agreeing on the complete unchanged
complement, and ONE certified strict global B-source-support drop.
It combines, for that SAME replacement:
* function-closedness of the transported outer context,
* injection of the ORIGINAL ordered outer root into that context,
* exact preservation of its original target coordinates, and
* a STRICT drop in B-exclusive SOURCE count INSIDE the context.

The inner piece must genuinely lie inside the old geometric outer
piece.  The original outer root must be outside the flipped inner
nonroot component.

This theorem is a concrete, reusable part of Track C's step relation.
It does NOT assert the transported context is again a minimal-
separator geometric piece or has the same complete all-test
incompatibility profile. Those two hypotheses remain outstanding.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- All already-verified contextual one-step certificates, tied
to a SINGLE actual full native functional inner replacement.

Unlike separate existential flip theorems, the output's four
conclusions concern the same `New`, `iQ`, `iE` and `g`.
The source support count is local to the transported context,
not global and not a count of target images. -/
theorem geometricInnerSubpiece_closed_fixedRoot_strictLocalRightSupport
    {V W UT : Type}
    [Finite V] [Finite W]
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hInnerInside :
      geometricPieceVertices Old d ⊆ geometricPieceVertices Old P)
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Old
        (Set.range d.roots) d.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old d).root)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old d).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old d).rootEmbedding iQ iE)
    (f : V → UT) (g : W → UT) (BOnly : Set UT)
    (hSameComplement :
      ∀ b : (geometricGlobalComplementChart Old d).Carrier,
        g (iE b) = f b.1)
    (hGlobalDrop :
      Nat.card {w : W // g w ∈ BOnly} <
        Nat.card {v : V // f v ∈ BOnly}) :
    New.IsClosed
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old P d)) ∧
    Function.Injective
      (fun i : Fin n =>
        iE (⟨P.roots i, hOuterRootOutside i⟩ :
          (geometricGlobalComplementChart Old d).Carrier)) ∧
    (∀ i : Fin n,
      iE (⟨P.roots i, hOuterRootOutside i⟩ :
        (geometricGlobalComplementChart Old d).Carrier) ∈
        (iQ '' (Set.univ : Set Q.Carrier) ∪
          iE '' (oldOuterContextInInnerComplement Old P d)) ∧
      g (iE (⟨P.roots i, hOuterRootOutside i⟩ :
        (geometricGlobalComplementChart Old d).Carrier)) = f (P.roots i)) ∧
    Nat.card {w : W //
      w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old P d)) ∧
      g w ∈ BOnly} <
    Nat.card {v : V //
      v ∈ geometricPieceVertices Old P ∧ f v ∈ BOnly} := by
  have hInnerRoot : ∀ i : Fin m,
      d.roots i ∈ geometricPieceVertices Old P := by
    intro i
    exact hInnerInside (Or.inl ⟨i, rfl⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact geometricOuterContext_closed_after_innerReplacement
      Old P d hInnerRoot Q New iQ iE hNewFree
  · intro i j hij
    apply P.roots_injective
    have hEqual : (⟨P.roots i, hOuterRootOutside i⟩ :
        (geometricGlobalComplementChart Old d).Carrier) =
      (⟨P.roots j, hOuterRootOutside j⟩ :
        (geometricGlobalComplementChart Old d).Carrier) :=
      iE.injective hij
    exact congrArg Subtype.val hEqual
  · intro i
    constructor
    · exact Or.inr
        (geometricOuterRoot_mem_closedContext_after_innerReplacement
          Old P d New iE hOuterRootOutside i)
    · exact hSameComplement
        (⟨P.roots i, hOuterRootOutside i⟩ :
          (geometricGlobalComplementChart Old d).Carrier)
  · exact geometricInnerSubpiece_strict_localRightSupport_of_global
      Old P d hInnerInside Q New iQ iE hNewFree
      f g BOnly hSameComplement hGlobalDrop

end AllThoseRamseyClasses.Lifts
