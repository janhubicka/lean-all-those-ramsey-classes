import AllThoseRamseyClasses.Applications.OrderedPosetHereditary
import AllThoseRamseyClasses.Published.InducedClosedLogicalDirection
import Mathlib.Tactic

/-!
# Exact original singleton and two-vertex tests for weak poset candidates

The corrected locally finite axiom does NOT assume its candidate
weak structure already belongs to the ambient ordered Ramsey class.
Instead, it assumes each closed U-irreducible INDUCED test belongs
to the actual K-class. For the empty closure description, every
induced test is intrinsically U-closed.

A source singleton is automatically ordinary irreducible. A pair
with a positive binary relation is ordinary irreducible, even if
the whole candidate's distinguished vertex order is incomplete.
This permits precise extraction of the reflexive partial-order
loops and the rule that each nontrivial positive p-edge has a
positive old order edge. These are indispensable inputs to the
previously verified poset exact-local completion (#214).

No global completion/class-Ramsey statement is asserted here.
-/

namespace AllThoseRamseyClasses.Applications.OrderedPosets

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published
open AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- An induced relation tuple on two old vertices retains
EXACTLY the original positive and negative relation information. -/
theorem weak_edge_induce_iff
    {V : Type} (C : RelStructure Lang V) (S : Set V)
    (R : Symbol) (a b : S) :
    edge (C.induce S) R a b ↔ edge C R a.1 b.1 := by
  have ht :
      (Subtype.val ∘ ![a, b] : Fin 2 → V) =
        ![a.1, b.1] := by
    funext i
    fin_cases i <;> rfl
  change C.rel R (Subtype.val ∘ ![a, b]) ↔
    C.rel R ![a.1, b.1]
  rw [ht]

/-- A binary relation between distinct old vertices witnesses
irreducibility on the EXACT two-vertex induced source, without
replacing this source by a closure or a target image. -/
theorem weak_pair_irreducible_of_positive_edge
    {V : Type} (C : RelStructure Lang V)
    (R : Symbol) (x y : V) (hne : x ≠ y)
    (hEdge : edge C R x y) :
    (C.induce ({x, y} : Set V)).Irreducible := by
  classical
  let S : Set V := {x, y}
  let sx : S := ⟨x, by simp [S]⟩
  let sy : S := ⟨y, by simp [S]⟩
  have hElem (a : S) : a = sx ∨ a = sy := by
    have ha : a.1 = x ∨ a.1 = y := by
      simpa only [S, Set.mem_insert_iff, Set.mem_singleton_iff] using a.2
    rcases ha with ha | ha
    · left; exact Subtype.ext ha
    · right; exact Subtype.ext ha
  have hRelation : (C.induce S).rel R ![sx, sy] :=
    (weak_edge_induce_iff C S R sx sy).mpr hEdge
  intro a b hab
  rcases hElem a with ha | ha <;> rcases hElem b with hb | hb
  · exact False.elim (hab (ha.trans hb.symm))
  · subst a
    subst b
    exact ⟨R, ![sx, sy], 0, 1, hRelation, rfl, rfl⟩
  · subst a
    subst b
    exact ⟨R, ![sx, sy], 1, 0, hRelation, rfl, rfl⟩
  · exact False.elim (hab (ha.trans hb.symm))

/-- Every structure is closed under the EMPTY closure description,
including a weak induced subset of any cardinality. -/
theorem isUClosed_empty_description
    {V : Type} (C : RelStructure Lang V) :
    IsUClosed (∅ : ClosureDescription Lang) C := by
  intro rule h
  simp at h

/-- Membership tests for the corrected class force every original
binary edge's exact two-vertex support to be an ordered poset. -/
theorem weak_pair_K_of_positive_edge
    {V : Type} (C : RelStructure Lang V)
    (hTests : CorrectedUIrreduciblesIn orderedPosetClass
      (∅ : ClosureDescription Lang) C)
    (R : Symbol) (x y : V) (hne : x ≠ y)
    (hEdge : edge C R x y) :
    orderedPosetClass (C.induce ({x, y} : Set V)) := by
  have hIrred : (C.induce ({x, y} : Set V)).Irreducible :=
    weak_pair_irreducible_of_positive_edge C R x y hne hEdge
  exact hTests ({x, y} : Set V)
    (isUClosed_empty_description _)
    (hIrred.isUIrreducible (∅ : ClosureDescription Lang))

/-- A singleton induced source is always ordinarily irreducible. -/
theorem weak_singleton_irreducible
    {V : Type} (C : RelStructure Lang V) (x : V) :
    (C.induce ({x} : Set V)).Irreducible := by
  intro a b hab
  exfalso
  apply hab
  apply Subtype.ext
  have ha : a.1 = x := by simpa only [Set.mem_singleton_iff] using a.2
  have hb : b.1 = x := by simpa only [Set.mem_singleton_iff] using b.2
  exact ha.trans hb.symm

/-- Every candidate covered by the corrected singleton tests has
the originally printed reflexive E-loop at EVERY vertex, even if
the candidate is not itself linearly ordered. -/
theorem weak_poset_reflexivity_from_tests
    {V : Type} (C : RelStructure Lang V)
    (hTests : CorrectedUIrreduciblesIn orderedPosetClass
      (∅ : ClosureDescription Lang) C) :
    ∀ x : V, edge C .equiv x x := by
  intro x
  let S : Set V := {x}
  have hIrred : (C.induce S).Irreducible :=
    weak_singleton_irreducible C x
  have hK : orderedPosetClass (C.induce S) :=
    hTests S (isUClosed_empty_description _)
      (hIrred.isUIrreducible (∅ : ClosureDescription Lang))
  have hLoop := hK.2.1 (⟨x, by simp [S]⟩ : S)
  exact (weak_edge_induce_iff C S .equiv _ _).mp hLoop

/-- On distinct vertices an original positive E-edge forces a
positive original strict order edge. This is NOT assumed globally
of arbitrary weak candidates; it follows from the exact corrected
irreducible-pair membership test. -/
theorem weak_poset_edge_implies_original_order
    {V : Type} (C : RelStructure Lang V)
    (hTests : CorrectedUIrreduciblesIn orderedPosetClass
      (∅ : ClosureDescription Lang) C)
    (x y : V) (hne : x ≠ y)
    (hEdge : edge C .equiv x y) :
    edge C .lt x y := by
  classical
  let S : Set V := {x, y}
  have hK : orderedPosetClass (C.induce S) :=
    weak_pair_K_of_positive_edge C hTests .equiv x y hne hEdge
  let sx : S := ⟨x, by simp [S]⟩
  let sy : S := ⟨y, by simp [S]⟩
  have hNe : sx ≠ sy := by
    intro h
    exact hne (congrArg Subtype.val h)
  have hPositive : edge (C.induce S) .equiv sx sy :=
    (weak_edge_induce_iff C S .equiv sx sy).mpr hEdge
  have hOrder := hK.2.2.2.2.1 sx sy hNe hPositive
  exact (weak_edge_induce_iff C S .lt sx sy).mp hOrder

end AllThoseRamseyClasses.Applications.OrderedPosets
