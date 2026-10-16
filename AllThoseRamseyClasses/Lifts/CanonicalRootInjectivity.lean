import AllThoseRamseyClasses.Lifts.FunctionalLiftLanguage
import AllThoseRamseyClasses.Lifts.ForbiddenGeometricFunctionalPieces

/-!
# The injective-root obligation in canonical functional lift relations

The 2019 canonical piece-lift predicate explicitly requires distinct
vertices of the rooted tuple, even though its realizing map is only
a weak homomorphism-embedding. A weak HE may identify nonadjacent
vertices; it does NOT automatically give root injectivity.

This file states the exact introduction and elimination lemmas:
a rooted weak realization produces a canonical lift relation when
the image of its ordered root tuple is injective. Full embeddings
supply this injectivity automatically.

For an ACTUAL geometrically selected piece of a forbidden source,
the weak map of the whole source restricts through the VERIFIED
closed functional piece inclusion. The remaining new obligation is
EXACTLY injectivity of the root image; the main proof's earlier
injective forbidden-witness reduction may provide it.

No unchecked root injectivity inference is made.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {W V : Type v}

/-- A weak rooted realization gives the corresponding canonical
extra relation, PROVIDED the image of the root tuple is injective. -/
theorem functionalCanonicalRelation_of_weakRootedWitness
    (I : Type u) (ar : I → ℕ)
    (pieces : ∀ i : I, Set (FunctionalRootedPattern.{u,v} L (ar i)))
    (A : Structure L W) (i : I)
    (P : FunctionalRootedPattern.{u,v} L (ar i))
    (hP : P ∈ pieces i)
    (f : P.Carrier → W)
    (hf : P.str.IsEHNHomomorphismEmbedding A f)
    (hRoots : Function.Injective (f ∘ P.root)) :
    (functionalCanonicalLiftOn L I ar pieces A).rel (.inr i)
      (f ∘ P.root) := by
  change FunctionalCanonicalExtraRelation L I ar pieces A i
    (f ∘ P.root)
  refine ⟨hRoots, P, hP, f, hf, ?_⟩
  intro j
  rfl

/-- A FULL embedding of a rooted source is always a valid canonical
relation witness: full injectivity restricts to the ordered roots. -/
theorem functionalCanonicalRelation_of_fullEmbedding
    (I : Type u) (ar : I → ℕ)
    (pieces : ∀ i : I, Set (FunctionalRootedPattern.{u,v} L (ar i)))
    (A : Structure L W) (i : I)
    (P : FunctionalRootedPattern.{u,v} L (ar i))
    (hP : P ∈ pieces i)
    (e : Structure.Embedding P.str A) :
    (functionalCanonicalLiftOn L I ar pieces A).rel (.inr i)
      (e ∘ P.root) :=
  functionalCanonicalRelation_of_weakRootedWitness I ar pieces
    A i P hP e e.isEHNHomomorphismEmbedding
      (e.injective.comp P.root_injective)

/-- Every canonical piece relation witness has pairwise distinct
root images. In particular the proof cannot derive this relation
from a weak HE alone when its root image has collisions. -/
theorem functionalCanonicalRelation_forces_injective
    (I : Type u) (ar : I → ℕ)
    (pieces : ∀ i : I, Set (FunctionalRootedPattern.{u,v} L (ar i)))
    (A : Structure L W) (i : I)
    (xs : Fin (ar i) → W)
    (h : (functionalCanonicalLiftOn L I ar pieces A).rel (.inr i) xs) :
    Function.Injective xs :=
  h.1

/-- The manuscript's geometric source-to-canonical-lift step,
with its previously implicit ROOT-INJECTIVITY premise explicit.

The map of the forbidden source may be weak globally. Its
restriction to the closed induced piece is a weak HE by
composition with the full geometric piece inclusion. -/
theorem functionalCanonicalRelation_of_geometricPiece
    (I : Type u) (ar : I → ℕ)
    (pieces : ∀ i : I, Set (FunctionalRootedPattern.{u,v} L (ar i)))
    (A : Structure L V)
    (i : I)
    (d : GeometricFunctionalPieceData A (ar i))
    (hP : geometricFunctionalRootedPattern A d ∈ pieces i)
    (Target : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding Target f)
    (hRoots : Function.Injective (f ∘ d.roots)) :
    (functionalCanonicalLiftOn L I ar pieces Target).rel (.inr i)
      (f ∘ d.roots) := by
  let P : FunctionalRootedPattern.{u,v} L (ar i) :=
    geometricFunctionalRootedPattern A d
  have hPiece :
      P.str.IsEHNHomomorphismEmbedding Target
        (fun x : P.Carrier => f x.1) := by
    exact hf.comp
      (geometricFunctionalPieceEmbedding A d).isEHNHomomorphismEmbedding
  have hCanonical := functionalCanonicalRelation_of_weakRootedWitness
    I ar pieces Target i P hP (fun x : P.Carrier => f x.1)
    hPiece hRoots
  exact hCanonical

end AllThoseRamseyClasses.Lifts
