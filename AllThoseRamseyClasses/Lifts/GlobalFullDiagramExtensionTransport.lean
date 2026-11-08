import AllThoseRamseyClasses.Lifts.GlobalSurjectiveFullEmbeddingInverse

/-!
# Track F: transport full extension witnesses through a commuting isomorphism square

The actual full finite-age Fraïssé schedule enumerates
labelled representative diagrams d:P↪Q. The genuine
finite extension property, however, must hold for ANY
finite full embedding i:A↪B, not merely the specific
enumerated representative arrows.

Suppose a:P↪A and b:Q↪B are SURJECTIVE FULL
set-valued-functional embeddings, and their diagram
commutes b∘d=i∘a. If a full embedding g:Q↪X
extends f∘a:P↪X along d, then it induces a genuine
FULL embedding h:B↪X extending f:A↪X along i.
The proof uses the verified inverse full embedding
b⁻¹:B↪Q, injectivity of b, and surjectivity of a.

This lemma is independent of first-order limits, root
injectivization, finite-generation closure, forbidden
families and language arity. It is the exact algebraic
transport needed to turn the *representative-diagram*
fair extension schedule into the full extension property.

Every map is FULL. Entire partial and set-valued function
fibres, nullary symbols, repeated entries and all old/new
relation truth values are preserved by construction.
The original 2019 numbered manuscript remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v₁ v₂ v₃ v₄ v₅
variable {L : Language.{u}}

/-- A witness of the finite extension property along one
FULL representative diagram can be transferred back to
an arbitrary isomorphic FULL extension diagram.

The two vertical maps a,b must be surjective FULL
embeddings; no weak/positive-only homomorphism is enough.
The result is a genuine FULL target embedding B↪X whose
restriction along i agrees pointwise with f. -/
theorem fullExtensionWitness_transportFromSurjectiveSquare
    {VP : Type v₁} {VQ : Type v₂}
    {VA : Type v₃} {VB : Type v₄} {VX : Type v₅}
    {P : Structure L VP} {Q : Structure L VQ}
    {A : Structure L VA} {B : Structure L VB}
    {X : Structure L VX}
    (d : Structure.Embedding P Q)
    (a : Structure.Embedding P A)
    (b : Structure.Embedding Q B)
    (ha : Function.Surjective a)
    (hb : Function.Surjective b)
    (i : Structure.Embedding A B)
    (hSquare : ∀ p : VP, b (d p) = i (a p))
    (f : Structure.Embedding A X)
    (g : Structure.Embedding Q X)
    (hDiagram : ∀ p : VP, g (d p) = f (a p)) :
    ∃ (h : Structure.Embedding B X),
      ∀ x : VA, h (i x) = f x := by
  let bInv : Structure.Embedding B Q :=
    fullEmbeddingInverseOfSurjective b hb
  refine ⟨g.comp bInv, ?_⟩
  intro x
  obtain ⟨p, hp⟩ := ha x
  have hLift : bInv (i x) = d p := by
    apply b.injective
    calc
      b (bInv (i x)) = i x :=
        fullEmbeddingInverseOfSurjective_rightInverse b hb (i x)
      _ = i (a p) := congrArg i hp.symm
      _ = b (d p) := (hSquare p).symm
  calc
    (g.comp bInv) (i x) = g (bInv (i x)) := rfl
    _ = g (d p) := congrArg g hLift
    _ = f (a p) := hDiagram p
    _ = f x := congrArg f hp

end AllThoseRamseyClasses.Lifts
