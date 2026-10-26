import AllThoseRamseyClasses.Lifts.GlobalFlipContextOutsideSupport
import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram

/-!
# Strict LOCAL right-exclusive support in an actual contextual inner flip

An inner genuine geometric source piece D=U∪C_D is fully contained
in an outer genuine piece P=R∪C_P. Its exact full native complement
E=Old\C_D contains all of the rest of P. The old source is an
ACTUAL full native free amalgam D +_U E.

The original outer set P is therefore EXACTLY
  (all vertices of D) ∪ (E-vertices whose old image is in P).
This is an equality of literal old source vertex sets, not an
assumption about a chosen target homomorphism-embedding.

Any genuine inner replacement New = Q' +_U E has the function-closed
transported outer context
  NewP := (all vertices of Q') ∪ (E-vertices whose old image is in P).

If the SAME actual old/new target maps agree on every retained
E-vertex, and their GLOBAL right-exclusive source support count
strictly decreases, the previously proved outside-support bijection
and finite partition theorem now force a STRICTLY DECREASING
RIGHT-exclusive SOURCE count INSIDE NewP versus old P.

This is the genuine local-count descent that is needed to iterate
Claim 2. The new context is not yet proved to be a genuine
minimal-separator geometric piece or to retain its old complete
Myhill--Nerode profile, so the full iteration remains open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An actual geometric inner piece D contained in a geometric
outer piece P gives the exact OLD source context decomposition
of P as (all of D) union (the part of P in the full complement E
of D). This is a literal equality, not merely an inclusion. -/
theorem geometricInnerSubpiece_oldOuterContext_eq
    {V : Type}
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hInnerInside :
      geometricPieceVertices Old d ⊆ geometricPieceVertices Old P) :
    ((functionalComponentEmbedding Old
        (Set.range d.roots) d.minimal.1 d.left) ''
        (Set.univ : Set (geometricGlobalFunctionalChart Old d).ext.Carrier)) ∪
      (functionalComponentComplementEmbedding Old
        (Set.range d.roots) d.minimal.1 d.left) ''
        (oldOuterContextInInnerComplement Old P d) =
      geometricPieceVertices Old P := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases hz with hzD | hzE
    · obtain ⟨a, _ha, rfl⟩ := hzD
      exact hInnerInside a.2
    · obtain ⟨b, hb, rfl⟩ := hzE
      exact hb
  · intro z hzP
    by_cases hzC :
        z ∈ functionalComponentFrom Old (Set.range d.roots) d.left
    · exact Or.inl
        ⟨⟨z, Or.inr hzC⟩, Set.mem_univ _, rfl⟩
    · exact Or.inr
        ⟨⟨z, hzC⟩, hzP, rfl⟩

/-- The LOCAL B-support strictly decreases inside the transported
outer context through an ACTUAL native inner-piece replacement.

Only the FULL source-complement preservation and a global strict
source-support certificate for the SAME old/new target maps are
assumed. There is no target-root or global weak-map injectivity
hypothesis. The old context is exactly the literal outer geometric
piece P, provided the inner piece is wholly contained inside P.

The new context is genuinely function-closed by #641 but is not
automatically a minimal-separator geometric piece. -/
theorem geometricInnerSubpiece_strict_localRightSupport_of_global
    {V W UT : Type}
    [Finite V] [Finite W]
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hInnerInside :
      geometricPieceVertices Old d ⊆ geometricPieceVertices Old P)
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
    Nat.card {w : W //
      w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old P d)) ∧
      g w ∈ BOnly} <
    Nat.card {v : V //
      v ∈ geometricPieceVertices Old P ∧ f v ∈ BOnly} := by
  let E := geometricGlobalComplementChart Old d
  letI : Finite E.Carrier :=
    Finite.of_injective (fun b : E.Carrier => b.1)
      (by intro a b hab; exact Subtype.ext hab)
  have hInnerRoot : ∀ i : Fin m,
      d.roots i ∈ geometricPieceVertices Old P := by
    intro i
    exact hInnerInside (Or.inl ⟨i, rfl⟩)
  have hLocalDrop :=
    fullFreeAmalgam_contextLocal_support_lt_of_global
      (geometricGlobalSource_freeDiagram Old d)
      hNewFree
      (oldOuterContextInInnerComplement Old P d)
      (oldOuterContext_contains_innerRoot Old P d hInnerRoot)
      f g BOnly
      (by intro b; change g (iE b) = f b.1; exact hSameComplement b)
      hGlobalDrop
  have hOldContextEq :=
    geometricInnerSubpiece_oldOuterContext_eq
      Old P d hInnerInside
  rw [← hOldContextEq]
  exact hLocalDrop

end AllThoseRamseyClasses.Lifts
