import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Track D: finite five-cycle root-collision regression

This is a **finite combinatorial certificate** for the obstruction in
LIFT-INJECTIVE-IMAGE-AUDIT-20261016.md of the paper repository.

The source is the chordless undirected five-cycle (with no ternary
relation). The target has the complete irreflexive graph on three
vertices and an extra ternary tuple (0,1,2). The weak map has colours
0,1,0,1,2. Every source irreducible graph test is a singleton or an
edge; on either, the map reflects both the binary relation and the
empty ternary relation. Yet the source root (0,2) COLLAPSES.

No injection of the five-cycle into the three-vertex target exists.
Any injective map from the triangle to this target hits the extra
ternary tuple, so cannot embed the triangle with empty ternary
relation fully.

IMPORTANT SCOPE: The graph/tuple assertions below are checked
directly on the finite carriers. A separate proof of closure of the
whole forbidden family {C3,C5} under *tuple-surjective* EHN images,
and a direct bridge to the native Structure.IsEHNHomomorphismEmbedding
API, are still required for a fully Lean-certified counterexample to
the unrestricted injectivization inference. Neither the actual
free-amalgam maximal-lift hypotheses nor strong amalgamation are
refuted by this regression. Never tag the full 2019 lift result as
verified on the strength of these finite checks.
-/

namespace AllThoseRamseyClasses.Lifts.RootCollisionFiveCycle

/-- The symmetric, loop-free five-cycle on Fin 5. -/
def cycle5Edge (a b : Fin 5) : Prop :=
  (a.val + 1) % 5 = b.val ∨ (b.val + 1) % 5 = a.val

/-- The symmetric, loop-free triangle on Fin 3. -/
def triangleEdge (a b : Fin 3) : Prop := a ≠ b

/-- The single extra ternary tuple in the target. -/
def extraTernary (a b c : Fin 3) : Prop :=
  a = 0 ∧ b = 1 ∧ c = 2

/-- An actual weak colouring that identifies the two separating
source-root vertices 0 and 2. -/
def weakColor (a : Fin 5) : Fin 3 :=
  if a = 0 ∨ a = 2 then 0
  else if a = 1 ∨ a = 3 then 1
  else 2

/-- Source edges are preserved by the weak map. -/
theorem weakColor_preserves_edges :
    ∀ a b : Fin 5, cycle5Edge a b →
      triangleEdge (weakColor a) (weakColor b) := by
  decide

/-- Each edge of the five-cycle is a FULL binary test: for the
two-element carrier picked out by its endpoints, the map reflects
the source edge relation and the target triangle relation. -/
theorem weakColor_full_binary_on_edge_tests :
    ∀ a b : Fin 5, cycle5Edge a b →
      ∀ u v : Bool,
        cycle5Edge (if u then a else b) (if v then a else b) ↔
        triangleEdge (weakColor (if u then a else b))
          (weakColor (if v then a else b)) := by
  decide

/-- The target's extra ternary tuple cannot be seen on the image
of a single source edge, no matter how the triple repeats endpoints. -/
theorem weakColor_no_extra_ternary_on_edge_tests :
    ∀ a b : Fin 5, cycle5Edge a b →
      ∀ u v w : Bool,
        ¬ extraTernary
          (weakColor (if u then a else b))
          (weakColor (if v then a else b))
          (weakColor (if w then a else b)) := by
  decide

/-- The C5 graph has no triple of pairwise adjacent distinct
vertices, hence its binary/empty-ternary irreducible full tests
cannot contain three distinct points. -/
theorem cycle5_no_triangle :
    ∀ a b c : Fin 5,
      ¬ (cycle5Edge a b ∧ cycle5Edge b c ∧ cycle5Edge c a) := by
  decide

/-- Exhaustive finite test of the same irreducible-source
cardinality fact, for ALL vertex subsets (not only named edges). -/
theorem cycle5_clique_at_most_two :
    ∀ S : Finset (Fin 5),
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → cycle5Edge a b) →
      S.card ≤ 2 := by
  decide

/-- The specific ordered root (0,2) is distinct in the source
but is not injective under the weak witness. -/
theorem weakColor_root_collision :
    weakColor (0 : Fin 5) = weakColor (2 : Fin 5) := by
  decide

theorem weakColor_not_injective : ¬ Function.Injective weakColor := by
  intro hinj
  have h : (0 : Fin 5) = 2 := hinj weakColor_root_collision
  exact (by decide : (0 : Fin 5) ≠ 2) h

/-- The two root coordinates separate 1 from 3, with explicit
witness paths after restoring either coordinate. This checks the
finite edge data; the general minimal-closed-separator statement
is not re-proved here. -/
theorem separator_root_edge_certificate :
    ¬ cycle5Edge 1 3 ∧ ¬ cycle5Edge 1 4 ∧
      cycle5Edge 1 2 ∧ cycle5Edge 2 3 ∧
      cycle5Edge 1 0 ∧ cycle5Edge 0 4 ∧
      cycle5Edge 4 3 := by
  decide

/-- An injection from five vertices to three is impossible,
independently of structure. -/
theorem no_injective_five_cycle_map
    (f : Fin 5 → Fin 3) : ¬ Function.Injective f := by
  intro hinj
  have hcard : Fintype.card (Fin 5) ≤ Fintype.card (Fin 3) :=
    Fintype.card_le_of_injective f hinj
  norm_num at hcard

/-- Every injection from the three-vertex empty-ternary triangle
onto the target must hit the added tuple somewhere. Only 27
maps need be checked. -/
theorem every_injective_triangle_map_hits_extra_ternary :
    ∀ f : Fin 3 → Fin 3, Function.Injective f →
      ∃ a b c : Fin 3, extraTernary (f a) (f b) (f c) := by
  decide

/-- Therefore NO injective map from the empty-ternary triangle
can reflect the target ternary relation. -/
theorem no_full_empty_ternary_triangle_map :
    ¬ ∃ f : Fin 3 → Fin 3, Function.Injective f ∧
      (∀ a b c : Fin 3, ¬ extraTernary (f a) (f b) (f c)) := by
  rintro ⟨f, hinj, hreflect⟩
  obtain ⟨a, b, c, htuple⟩ :=
    every_injective_triangle_map_hits_extra_ternary f hinj
  exact hreflect a b c htuple

end AllThoseRamseyClasses.Lifts.RootCollisionFiveCycle
