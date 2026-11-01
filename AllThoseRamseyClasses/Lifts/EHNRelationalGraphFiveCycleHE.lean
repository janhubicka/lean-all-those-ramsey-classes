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
      have hed : cycle5Edge (z 0).1 (z 1).1 := hrel
      fin_cases i
      · fin_cases j
        · exact False.elim (hab (ha.symm.trans hb))
        · have h0 : (z 0).1 = x := congrArg Subtype.val ha
          have h1 : (z 1).1 = y := congrArg Subtype.val hb
          simpa only [h0, h1] using hed
      · fin_cases j
        · have h0 : (z 0).1 = y := congrArg Subtype.val hb
          have h1 : (z 1).1 = x := congrArg Subtype.val ha
          have hs : cycle5Edge (z 1).1 (z 0).1 := by
            simpa only [cycle5Edge, or_comm] using hed
          simpa only [h0, h1] using hs
        · exact False.elim (hab (ha.symm.trans hb))
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
        exact weakColor_preserves_edges (xs 0) (xs 1) hrel
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
        have hDiff : xs 0 ≠ xs 1 := by
          intro h
          have hCol : weakColor (xs 0) ≠ weakColor (xs 1) :=
            hTarget
          exact hCol (congrArg weakColor h)
        exact cycle5_adjacent_of_graphTestIrreducible
          S hS (xs 0) (xs 1) (hxs 0) (hxs 1) hDiff
      | true =>
        have hExtra :
            extraTernary
              (weakColor (xs 0))
              (weakColor (xs 1))
              (weakColor (xs 2)) := hTarget
        obtain ⟨h0, h1, h2⟩ := hExtra
        have h01 : xs 0 ≠ xs 1 := by
          intro h
          have hc : (0 : Fin 3) = 1 :=
            h0.symm.trans ((congrArg weakColor h).trans h1)
          exact (by decide : (0 : Fin 3) ≠ 1) hc
        have h12 : xs 1 ≠ xs 2 := by
          intro h
          have hc : (1 : Fin 3) = 2 :=
            h1.symm.trans ((congrArg weakColor h).trans h2)
          exact (by decide : (1 : Fin 3) ≠ 2) hc
        have h20 : xs 2 ≠ xs 0 := by
          intro h
          have hc : (2 : Fin 3) = 0 :=
            h2.symm.trans ((congrArg weakColor h).trans h0)
          exact (by decide : (2 : Fin 3) ≠ 0) hc
        have e01 := cycle5_adjacent_of_graphTestIrreducible
          S hS (xs 0) (xs 1) (hxs 0) (hxs 1) h01
        have e12 := cycle5_adjacent_of_graphTestIrreducible
          S hS (xs 1) (xs 2) (hxs 1) (hxs 2) h12
        have e20 := cycle5_adjacent_of_graphTestIrreducible
          S hS (xs 2) (xs 0) (hxs 2) (hxs 0) h20
        exact False.elim
          (cycle5_no_triangle (xs 0) (xs 1) (xs 2)
            ⟨e01, e12, e20⟩)
    | inr F =>
      exact Empty.elim F

end AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap
