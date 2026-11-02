import AllThoseRamseyClasses.Lifts.EHNFiveCycleImageClosedFamily
import AllThoseRamseyClasses.Lifts.WeakFunctionalGaifmanProjection
import AllThoseRamseyClasses.Lifts.GlobalConnectedForbiddenJEP
import Mathlib.Tactic

/-!
# Track D: connectedness of the five-cycle-generated forbidden image family

The original Section 3 lift theorem assumes that every forbidden
source is finite and connected. For the countercheck family of all
vertex- and tuple-surjective original-partial HE images of C5,
finiteness is already certified by the surjective five-element
source map. This module certifies connectedness in the EXACT native
Gaifman graph of the functional language.

The key generic tool works for arbitrary native relation/function
languages and does not assume injectivity: a weak homomorphism
takes each Gaifman edge either to an edge or a collapsed vertex,
and hence takes paths to paths. A vertex-surjective weak image
of a connected source is connected.

The five-cycle itself has explicit paths from vertex 0 to each
vertex using its actual positive binary relation. Every member
of fiveCycleImageFamily is therefore finite, nonempty and connected.

This does not turn the arbitrary-target injectivization obstruction
into a counterexample to maximal-lift strong amalgamation. The
latter has extra hypotheses not satisfied by the three-point target.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Weak functional homomorphisms preserve actual native
Gaifman reachability, allowing edge collapse but never breaking
a path. Works for all arities and nullary symbols. -/
theorem weakGaifmanReach_map
    {V W : Type}
    {A : Structure L V} {B : Structure L W}
    {f : V → W}
    (hf : A.IsWeakHomomorphism B f)
    {x y : V}
    (hReach : Relation.ReflTransGen
      (GaifmanAdjacent A.graph) x y) :
    Relation.ReflTransGen
      (GaifmanAdjacent B.graph) (f x) (f y) := by
  induction hReach with
  | refl =>
    exact Relation.ReflTransGen.refl
  | @tail a b hpath hedge ih =>
    rcases weakFunctionalGaifmanAdjacent_map hf hedge with
      heq | hImageEdge
    · exact heq ▸ ih
    · exact ih.tail hImageEdge

/-- Surjective weak images of nonempty connected sources
are nonempty and connected. No global injectivity and
no full embedding of the image are assumed. -/
theorem weakSurjectiveImage_connectedNonempty
    {V W : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsWeakHomomorphism B f)
    (hSource : Nonempty V ∧
      ∀ x y : V, Relation.ReflTransGen
        (GaifmanAdjacent A.graph) x y)
    (hSurj : Function.Surjective f) :
    Nonempty W ∧
      ∀ x y : W, Relation.ReflTransGen
        (GaifmanAdjacent B.graph) x y := by
  obtain ⟨x⟩ := hSource.1
  refine ⟨⟨f x⟩, ?_⟩
  intro u v
  obtain ⟨a, rfl⟩ := hSurj u
  obtain ⟨b, rfl⟩ := hSurj v
  exact weakGaifmanReach_map hf (hSource.2 a b)

end AllThoseRamseyClasses.Lifts

namespace AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Lifts.RootCollisionFiveCycle

private def c5Edge0 :
    Fin (language.graph.arity (.inl false)) := ⟨0, by decide⟩

private def c5Edge1 :
    Fin (language.graph.arity (.inl false)) := ⟨1, by decide⟩

private theorem c5Edge10 : c5Edge1 ≠ c5Edge0 := by decide

/-- Each source cycle edge is a genuine native Gaifman
edge, witnessed by the *complete original relation tuple*. -/
theorem cycle5Edge_gaifman
    {x y : Fin 5}
    (h : cycle5Edge x y) :
    GaifmanAdjacent cycle5.graph x y := by
  have hxy : x ≠ y := by
    intro hEq
    subst y
    have hNoLoop : ∀ a : Fin 5, ¬ cycle5Edge a a := by decide
    exact hNoLoop x h
  let t : Fin (language.graph.arity (.inl false)) → Fin 5 :=
    fun i => if i = c5Edge0 then x else y
  have hRel : cycle5.graph.rel (.inl false) t := by
    change cycle5Edge (t c5Edge0) (t c5Edge1)
    simpa [t, c5Edge10] using h
  refine ⟨hxy, .inl false, t, c5Edge0, c5Edge1,
    hRel, ?_, ?_⟩
  · simp [t]
  · simp [t, c5Edge10]

private theorem cycle5Reach_symm
    {x y : Fin 5}
    (h : Relation.ReflTransGen
      (GaifmanAdjacent cycle5.graph) x y) :
    Relation.ReflTransGen
      (GaifmanAdjacent cycle5.graph) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b hab hedge ih =>
    exact (Relation.ReflTransGen.single hedge.symm).trans ih

/-- Explicit paths from vertex 0 to every source vertex. -/
theorem cycle5_reachable_from_zero
    (x : Fin 5) :
    Relation.ReflTransGen (GaifmanAdjacent cycle5.graph)
      0 x := by
  have h01 : Relation.ReflTransGen (GaifmanAdjacent cycle5.graph)
      0 1 := Relation.ReflTransGen.single
        (cycle5Edge_gaifman (by decide : cycle5Edge 0 1))
  have h12 : Relation.ReflTransGen (GaifmanAdjacent cycle5.graph)
      1 2 := Relation.ReflTransGen.single
        (cycle5Edge_gaifman (by decide : cycle5Edge 1 2))
  have h04 : Relation.ReflTransGen (GaifmanAdjacent cycle5.graph)
      0 4 := Relation.ReflTransGen.single
        (cycle5Edge_gaifman (by decide : cycle5Edge 0 4))
  have h43 : Relation.ReflTransGen (GaifmanAdjacent cycle5.graph)
      4 3 := Relation.ReflTransGen.single
        (cycle5Edge_gaifman (by decide : cycle5Edge 4 3))
  fin_cases x
  · exact Relation.ReflTransGen.refl
  · exact h01
  · exact h01.trans h12
  · exact h04.trans h43
  · exact h04

/-- The original five-cycle is nonempty and connected in
its complete native relation/function Gaifman graph. -/
theorem cycle5_connectedNonempty :
    Nonempty (Fin 5) ∧
      ∀ x y : Fin 5,
        Relation.ReflTransGen
          (GaifmanAdjacent cycle5.graph) x y := by
  refine ⟨⟨0⟩, ?_⟩
  intro x y
  exact (cycle5Reach_symm (cycle5_reachable_from_zero x)).trans
    (cycle5_reachable_from_zero y)

/-- The source-generated image family meets the original
connectedness and nonemptiness hypotheses of Section 3,
in addition to its previously checked finite carrier property.
The actual strong-amalgamation lemma is not concluded. -/
theorem fiveCycleImageFamily_connectedNonempty :
    GlobalForbiddenSourcesConnectedNonempty
      (L := language) fiveCycleImageFamily := by
  intro U P _ hP
  obtain ⟨f, hfSurj, hfHE, _⟩ := hP
  exact weakSurjectiveImage_connectedNonempty
    cycle5 P f hfHE.toEHN.1
    cycle5_connectedNonempty hfSurj

end AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap
