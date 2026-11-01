import AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap
import PartiteConstruction.Relational.Homomorphism

/-!
# Track D: the C5/T map is a genuine homomorphism-embedding on its relational graph

The earlier finite native regression established that the map
C5 → triangle+T is positive, surjective on vertices, and fails
tuple-surjectivity onto the complete induced range. It left
the local irreducible-test restriction unproved.

In the RELATIONAL graph language, every irreducible induced test
is a clique. As the source five-cycle is triangle-free, each
irreducible induced test has at most two vertices. The explicit
colouring is a full embedding on every source edge and every
one-point test, and the added ternary target tuple cannot be
seen by any such test. Therefore it is a genuine relational
homomorphism-embedding, not merely a positive homomorphism.

This is source-matched to the original ordinary-relational
homomorphism-embedding convention. The native universal
function-language EHN bridge is handled separately and should
not be inferred just from source positive preservation.

The source-generated Q contains a forbidden triangle whose
full embedding into the target is blocked by the additional T
tuple. This refutes the blanket injectivization sentence for
arbitrary targets, NOT the maximal-common-lift free-amalgamation
theorem.
-/

namespace AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Lifts.RootCollisionFiveCycle

/-! Explicit tuple indices avoid fragile typeclass synthesis of
    Fin (language.graph.arity (.inl R)) in the nested graph language. -/
private theorem edgeArity :
    language.graph.arity (.inl false) = 2 := by decide

private theorem ternaryArity :
    language.graph.arity (.inl true) = 3 := by decide

private def edge0 : Fin (language.graph.arity (.inl false)) :=
  ⟨0, by rw [edgeArity]; decide⟩

private def edge1 : Fin (language.graph.arity (.inl false)) :=
  ⟨1, by rw [edgeArity]; decide⟩

private def tern0 : Fin (language.graph.arity (.inl true)) :=
  ⟨0, by rw [ternaryArity]; decide⟩

private def tern1 : Fin (language.graph.arity (.inl true)) :=
  ⟨1, by rw [ternaryArity]; decide⟩

private def tern2 : Fin (language.graph.arity (.inl true)) :=
  ⟨2, by rw [ternaryArity]; decide⟩

private theorem edgeIndex_cases
    (i : Fin (language.graph.arity (.inl false))) :
    i = edge0 ∨ i = edge1 := by
  have hi : i.val < 2 := by simpa only [edgeArity] using i.isLt
  have h : i.val = 0 ∨ i.val = 1 := by omega
  rcases h with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

/-- On a source irreducible RELATIONAL graph test, any two
distinct vertices must be adjacent in the five-cycle. The
ternary source relation is empty and there are no functions. -/
theorem cycle5_adjacent_of_graphTestIrreducible
    (S : Set (Fin 5))
    (hS : (cycle5.graph.induce S).Irreducible)
    (x y : Fin 5) (hx : x ∈ S) (hy : y ∈ S)
    (hxy : x ≠ y) : cycle5Edge x y := by
  let a : S := ⟨x, hx⟩
  let b : S := ⟨y, hy⟩
  have hab : a ≠ b := by
    intro h
    exact hxy (congrArg Subtype.val h)
  obtain ⟨R, z, i, j, hrel, ha, hb⟩ := hS hab
  cases R with
  | inl R =>
    cases R with
    | false =>
      have hed : cycle5Edge (z edge0).1 (z edge1).1 := by
        change cycle5Edge (z edge0).1 (z edge1).1 at hrel
        exact hrel
      rcases edgeIndex_cases i with hi | hi <;>
        rcases edgeIndex_cases j with hj | hj
      · have hij : i = j := hi.trans hj.symm
        exact False.elim (hab (ha.symm.trans (hij ▸ hb)))
      · have h0 : (z edge0).1 = x := by
          exact congrArg Subtype.val (hi ▸ ha)
        have h1 : (z edge1).1 = y := by
          exact congrArg Subtype.val (hj ▸ hb)
        simpa only [h0, h1] using hed
      · have h0 : (z edge0).1 = y := by
          exact congrArg Subtype.val (hj ▸ hb)
        have h1 : (z edge1).1 = x := by
          exact congrArg Subtype.val (hi ▸ ha)
        have hs : cycle5Edge (z edge1).1 (z edge0).1 := by
          simpa only [cycle5Edge, or_comm] using hed
        simpa only [h0, h1] using hs
      · have hij : i = j := hi.trans hj.symm
        exact False.elim (hab (ha.symm.trans (hij ▸ hb)))
    | true =>
      exact False.elim hrel
  | inr F =>
    exact Empty.elim F

/-- The original weak colouring is a genuine RELATIONAL
homomorphism-embedding on the function-graph encoding. All
irreducible induced source tests are embedded fully, including
reflection of the target's extra ternary relation. -/
theorem weakColor_graphHomomorphismEmbedding :
    cycle5.graph.IsHomomorphismEmbedding
      triangleExtraTernary.graph weakColor := by
  apply RelStructure.IsHomomorphismEmbedding.of_map_reflect
  · intro R xs hrel
    cases R with
    | inl R =>
      cases R with
      | false =>
        change cycle5Edge (xs edge0) (xs edge1) at hrel
        change triangleEdge (weakColor (xs edge0))
          (weakColor (xs edge1))
        exact weakColor_preserves_edges (xs edge0) (xs edge1) hrel
      | true =>
        exact False.elim hrel
    | inr F =>
      exact Empty.elim F
  · intro S hS x hx y hy hEq
    by_contra hxy
    have hEdge :=
      cycle5_adjacent_of_graphTestIrreducible S hS x y hx hy hxy
    have hDistinct :=
      weakColor_preserves_edges x y hEdge
    exact hDistinct hEq
  · intro S hS R xs hxs hTarget
    cases R with
    | inl R =>
      cases R with
      | false =>
        change triangleEdge (weakColor (xs edge0))
          (weakColor (xs edge1)) at hTarget
        change cycle5Edge (xs edge0) (xs edge1)
        have hDiff : xs edge0 ≠ xs edge1 := by
          intro h
          have hCol : weakColor (xs edge0) ≠ weakColor (xs edge1) :=
            hTarget
          exact hCol (congrArg weakColor h)
        exact cycle5_adjacent_of_graphTestIrreducible
          S hS (xs edge0) (xs edge1) (hxs edge0) (hxs edge1) hDiff
      | true =>
        change extraTernary (weakColor (xs tern0))
          (weakColor (xs tern1)) (weakColor (xs tern2)) at hTarget
        have hExtra :
            extraTernary
              (weakColor (xs tern0))
              (weakColor (xs tern1))
              (weakColor (xs tern2)) := hTarget
        obtain ⟨h0, h1, h2⟩ := hExtra
        have h01 : xs tern0 ≠ xs tern1 := by
          intro h
          have hc : (0 : Fin 3) = 1 :=
            h0.symm.trans ((congrArg weakColor h).trans h1)
          exact (by decide : (0 : Fin 3) ≠ 1) hc
        have h12 : xs tern1 ≠ xs tern2 := by
          intro h
          have hc : (1 : Fin 3) = 2 :=
            h1.symm.trans ((congrArg weakColor h).trans h2)
          exact (by decide : (1 : Fin 3) ≠ 2) hc
        have h20 : xs tern2 ≠ xs tern0 := by
          intro h
          have hc : (2 : Fin 3) = 0 :=
            h2.symm.trans ((congrArg weakColor h).trans h0)
          exact (by decide : (2 : Fin 3) ≠ 0) hc
        have e01 := cycle5_adjacent_of_graphTestIrreducible
          S hS (xs tern0) (xs tern1) (hxs tern0) (hxs tern1) h01
        have e12 := cycle5_adjacent_of_graphTestIrreducible
          S hS (xs tern1) (xs tern2) (hxs tern1) (hxs tern2) h12
        have e20 := cycle5_adjacent_of_graphTestIrreducible
          S hS (xs tern2) (xs tern0) (hxs tern2) (hxs tern0) h20
        exact False.elim
          (cycle5_no_triangle (xs tern0) (xs tern1) (xs tern2)
            ⟨e01, e12, e20⟩)
    | inr F =>
      exact Empty.elim F

end AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap
