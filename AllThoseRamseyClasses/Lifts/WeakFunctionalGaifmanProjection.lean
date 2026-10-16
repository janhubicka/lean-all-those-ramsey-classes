import AllThoseRamseyClasses.Lifts.GaifmanCuts
import PartiteConstruction.Structure.Relationalize
import PartiteConstruction.Structure.GeneratedWeakHomImage

/-!
# Weak functional maps preserve Gaifman adjacency up to collapse

A weak homomorphism preserves every positive original relation
tuple and every genuine function input/output incidence. Therefore
it is a homomorphism of the RELATIONAL graph encodings, even
though it need not be a FULL function-fibre homomorphism.

In particular, a Gaifman edge in the source either collapses
to one target vertex or gives a Gaifman edge in the target.
This is a basic invariant of the original 2019 functional
homomorphism language and a prerequisite for proving that
weak forbidden-source Gaifman components cannot cross the
two exclusive sides of a free-amalgam target.

No injectivity of the weak map is assumed or inferred.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v

/-- Every weak functional homomorphism is a homomorphism on
the complete relational graph encoding of its function tuples. -/
theorem weakFunctionalGraph_homomorphism
    {L : Language.{u}} {V W : Type v}
    {A : Structure L V} {B : Structure L W}
    {f : V → W}
    (hf : A.IsWeakHomomorphism B f) :
    A.graph.IsHomomorphism B.graph f := by
  intro R xs hR
  cases R with
  | inl S =>
      exact hf.1 S xs hR
  | inr F =>
      change (xs (Fin.last (L.funcArity F))) ∈
        A.func F (fun i => xs i.castSucc) at hR
      change f (xs (Fin.last (L.funcArity F))) ∈
        B.func F (fun i => f (xs i.castSucc))
      exact hf.2 F (fun i => xs i.castSucc)
        (xs (Fin.last (L.funcArity F))) hR

/-- An adjacent pair of distinct source vertices remains adjacent
unless the weak map collapses the endpoints. All relation and
function graph incidences are included, even for nullary symbols. -/
theorem weakFunctionalGaifmanAdjacent_map
    {L : Language.{u}} {V W : Type v}
    {A : Structure L V} {B : Structure L W}
    {f : V → W}
    (hf : A.IsWeakHomomorphism B f)
    {x y : V}
    (hxy : GaifmanAdjacent A.graph x y) :
    f x = f y ∨ GaifmanAdjacent B.graph (f x) (f y) := by
  obtain ⟨_hne, R, xs, i, j, htuple, hx, hy⟩ := hxy
  by_cases hEq : f x = f y
  · exact Or.inl hEq
  · right
    refine ⟨hEq, R, f ∘ xs, i, j, ?_, ?_, ?_⟩
    · exact weakFunctionalGraph_homomorphism hf R xs htuple
    · exact congrArg f hx
    · exact congrArg f hy

/-- If the weak map is injective on two vertices, their adjacency
projects to a genuine target Gaifman edge. This is a LOCAL condition,
not global map injectivity. -/
theorem weakFunctionalGaifmanAdjacent_of_images_distinct
    {L : Language.{u}} {V W : Type v}
    {A : Structure L V} {B : Structure L W}
    {f : V → W}
    (hf : A.IsWeakHomomorphism B f)
    {x y : V}
    (hxy : GaifmanAdjacent A.graph x y)
    (hDistinct : f x ≠ f y) :
    GaifmanAdjacent B.graph (f x) (f y) := by
  rcases weakFunctionalGaifmanAdjacent_map hf hxy with h | h
  · exact False.elim (hDistinct h)
  · exact h

end AllThoseRamseyClasses.Lifts
