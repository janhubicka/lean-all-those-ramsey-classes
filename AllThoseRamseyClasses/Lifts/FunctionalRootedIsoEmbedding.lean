import AllThoseRamseyClasses.Lifts.ForbiddenGeometricFunctionalPieces

/-!
# Root-preserving graph isomorphisms are FULL functional isomorphisms

The lift construction identifies two functional rooted pieces by an
ordered-root preserving isomorphism of their complete function graphs.
This really is a full functional isomorphism: positive function graph
incidences preserve AND REFLECT the entire function value set, with
bijectivity supplying inverse transport of target values.

This lemma prevents an unnoticed change of root domains or old
function interpretations when transporting the geometric forbidden
pieces into a common fixed full functional root chart.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {n : ℕ}
variable {P Q : FunctionalRootedPattern.{u,v} L n}

/-- A full functional embedding induced by an ordered-root
isomorphism of the relation/function graph encodings.
No positivity assumption on function arities is made. -/
def FunctionalRootedPatternIso.toFullEmbedding
    (e : FunctionalRootedPatternIso P Q) :
    Structure.Embedding P.str Q.str where
  toFun := e.equiv
  injective := e.equiv.injective
  map_rel_iff := by
    intro R xs
    exact e.rel_iff (.inl R) xs
  map_func := by
    intro F xs
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hp : P.str.graph.rel (.inr F)
          (Structure.funcTuple xs z) :=
        (Structure.graph_func_snoc P.str F xs z).mpr hz
      have hq := (e.rel_iff (.inr F)
        (Structure.funcTuple xs z)).mpr hp
      change Q.str.graph.rel (.inr F)
        (e.equiv ∘ Structure.funcTuple xs z) at hq
      have htuple : e.equiv ∘ Structure.funcTuple xs z =
          Structure.funcTuple (e.equiv ∘ xs) (e.equiv z) :=
        Structure.comp_funcTuple e.equiv xs z
      have hq' : Q.str.graph.rel (.inr F)
          (Structure.funcTuple (e.equiv ∘ xs) (e.equiv z)) :=
        htuple ▸ hq
      exact (Structure.graph_func_snoc Q.str F
        (e.equiv ∘ xs) (e.equiv z)).mp hq'
    · intro hy
      obtain ⟨z, rfl⟩ := e.equiv.surjective y
      have hq : Q.str.graph.rel (.inr F)
          (Structure.funcTuple (e.equiv ∘ xs) (e.equiv z)) :=
        (Structure.graph_func_snoc Q.str F
          (e.equiv ∘ xs) (e.equiv z)).mpr hy
      have htuple : e.equiv ∘ Structure.funcTuple xs z =
          Structure.funcTuple (e.equiv ∘ xs) (e.equiv z) :=
        Structure.comp_funcTuple e.equiv xs z
      have hq' : Q.str.graph.rel (.inr F)
          (e.equiv ∘ Structure.funcTuple xs z) :=
        htuple.symm ▸ hq
      have hp : P.str.graph.rel (.inr F)
          (Structure.funcTuple xs z) :=
        (e.rel_iff (.inr F) (Structure.funcTuple xs z)).mp hq'
      exact ⟨z, (Structure.graph_func_snoc P.str F xs z).mp hp, rfl⟩

/-- The underlying full functional embedding is ONTO. -/
theorem FunctionalRootedPatternIso.toFullEmbedding_surjective
    (e : FunctionalRootedPatternIso P Q) :
    Function.Surjective e.toFullEmbedding :=
  e.equiv.surjective

/-- Ordered root coordinates are preserved by the corresponding
full functional embedding, not merely as an unlabelled set. -/
theorem FunctionalRootedPatternIso.toFullEmbedding_root
    (e : FunctionalRootedPatternIso P Q) (i : Fin n) :
    e.toFullEmbedding (P.root i) = Q.root i :=
  e.roots i

/-- The inverse rooted isomorphism also gives an onto full
functional embedding, and the two compositions are the identity
on the underlying carriers. -/
theorem FunctionalRootedPatternIso.inverse_on_vertices
    (e : FunctionalRootedPatternIso P Q) (x : P.Carrier) :
    (FunctionalRootedPatternIso.toFullEmbedding (P := Q) (Q := P) e.symm)
      (e.toFullEmbedding x) = x :=
  e.equiv.symm_apply_apply x

end AllThoseRamseyClasses.Lifts
