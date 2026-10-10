import AllThoseRamseyClasses.Published.OrderedRootCuts

/-!
# Strict rank inequalities needed for amalgamating linear orders

The canonical finite order extension sorts vertices by their
root cut (number of embedded root vertices preceding them),
then by the side-specific position. Root vertices are placed
AFTER side-only vertices with the SAME cut. This is forced by
the strict inequality proved below: if a root vertex precedes
a point, then the point has strictly greater root-cut rank.

Also, within each side the number of predecessors is strictly
monotone, so sorting by this finite rank preserves every original
strict side order. These are unbounded Lean facts about arbitrary
finite ordered paired structures, not finite regression data.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The rank of a vertex in its own finite strict linear order. -/
noncomputable def sideOrderRank
    {X : Type} [Fintype X]
    (Side : RelStructure Lang X) (x : X) : ℕ := by
  classical
  exact ((Finset.univ : Finset X).filter
    (fun y => edge Side .lt y x)).card

/-- The predecessor rank is strictly increasing in the original
side order. Hence it may be used as a stable tie-breaker in
the completed amalgam order. -/
theorem sideOrderRank_strictMono
    {X : Type} [Fintype X]
    (Side : RelStructure Lang X) (hSide : pairedClass Side)
    {x y : X} (hxy : edge Side .lt x y) :
    sideOrderRank Side x < sideOrderRank Side y := by
  classical
  unfold sideOrderRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  refine ⟨x, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hSide.lt_irrefl x
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_filter,
      Finset.mem_univ, true_and] at hz ⊢
    rcases hz with rfl | hzx
    · exact hxy
    · exact hSide.lt_trans z x y hzx hxy

/-- A root vertex preceding a vertex of one side forces a STRICT
increase in the number of root vertices below it.
In particular a root vertex can never precede a side-only
vertex with the same root-cut index. -/
theorem rootCut_strict_after_root
    {D X : Type} [Fintype D]
    {Root : RelStructure Lang D} {Side : RelStructure Lang X}
    (hSide : pairedClass Side)
    (s : Embedding Root Side) (d : D) (x : X)
    (h : edge Side .lt (s d) x) :
    rootCut Side s (s d) < rootCut Side s x := by
  classical
  unfold rootCut
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  refine ⟨d, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hSide.lt_irrefl (s d)
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_filter,
      Finset.mem_univ, true_and] at hz ⊢
    rcases hz with rfl | hzd
    · exact h
    · exact hSide.lt_trans (s z) (s d) x hzd h

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
