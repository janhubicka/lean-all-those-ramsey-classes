import AllThoseRamseyClasses.Published.CoordinatedCycleGapCount
import AllThoseRamseyClasses.Published.CoordinatedCycleGadgetWitness
import AllThoseRamseyClasses.Published.FinitePairedClass
import Mathlib.Tactic

/-!
# An actual finite K-target for every weak vertex subset of Ck

The long-cycle Ck is not a member of K because its E relation
is not transitive and its order is partial. For EVERY exact weak
vertex subset S we construct a finite ordered perfect-matching
structure D(k,S), on the ENTIRE finite carrier CycleVertex k.

The new E relation is equality of explicit component tags:
 - backbone blocks: (0, number of absent backbone blocks before i);
 - the closing T block: (0,0), like the first backbone block;
 - each edge-private D block: (1, its own block index).

The new order sorts first by its C0 control-vertex label, then by
block index to break any remaining ties. This is strict and total,
and extends all positive order tuples of the source Ck.

The matching relation is unchanged. Consequently D(k,S) lies in
the ORIGINAL finite ordered-paired-equivalence class K, without
requiring S to be U-closed. The remaining requirement for (4c) is
to show that the canonical weak inclusion S -> D(k,S) preserves
positive tuples and reflects all tuples on CLOSED irreducible tests.
That relation-reflection proof is a separate module.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The indices of all matching blocks actually met by an EXACT
weak test; even a single unmatched root makes its block present. -/
def cycleWeakPresentBlocks (k : ℕ)
    (S : Finset (CycleVertex k)) : Finset ℕ :=
  S.image (fun v => v.1.val)

/-- Explicit equivalence-class label of a block in the proposed
completion. The T block joins the first backbone E component;
each D block gets its own fresh class. -/
def cycleWeakEClass (k : ℕ) (S : Finset (CycleVertex k))
    (v : CycleVertex k) : ℕ × ℕ :=
  if v.1.val < cycleBackboneCount k then
    (0, cycleGapCount (cycleWeakPresentBlocks k S) v.1.val)
  else if v.1.val = cycleBlockCount k - 1 then (0,0)
  else (1,v.1.val)

/-- Complete order: C0 control labels have priority; ties are
broken by the actual block index. -/
def cycleWeakOrderLess (k : ℕ)
    (x y : CycleVertex k) : Prop :=
  (cycleControlVertex k x).val < (cycleControlVertex k y).val ∨
    ((cycleControlVertex k x).val = (cycleControlVertex k y).val ∧
      x.1.val < y.1.val)

theorem cycleWeakOrderLess_irrefl (k : ℕ) (x : CycleVertex k) :
    ¬ cycleWeakOrderLess k x x := by
  simp [cycleWeakOrderLess]

theorem cycleWeakOrderLess_trans (k : ℕ)
    (x y z : CycleVertex k)
    (hxy : cycleWeakOrderLess k x y)
    (hyz : cycleWeakOrderLess k y z) :
    cycleWeakOrderLess k x z := by
  dsimp [cycleWeakOrderLess] at *
  rcases hxy with h | h <;> rcases hyz with h' | h' <;> omega

/-- Control value plus matching-block identity uniquely identifies
a vertex: its control's parity also remembers the bit of its pair. -/
theorem cycleControlVertex_block_injective (k : ℕ)
    (x y : CycleVertex k)
    (hc : cycleControlVertex k x = cycleControlVertex k y)
    (hb : x.1 = y.1) : x = y := by
  rcases x with ⟨a,i⟩
  rcases y with ⟨b,j⟩
  change a = b at hb
  subst b
  have hv := congrArg (fun z : Fin 10 => z.val) hc
  change 2 * cycleBlockLabel k a + i.val =
    2 * cycleBlockLabel k a + j.val at hv
  have hij : i = j := Fin.ext (Nat.add_left_cancel hv)
  subst j
  rfl

theorem cycleWeakOrderLess_total (k : ℕ)
    (x y : CycleVertex k) (hxy : x ≠ y) :
    cycleWeakOrderLess k x y ∨ cycleWeakOrderLess k y x := by
  by_cases hc : (cycleControlVertex k x).val =
      (cycleControlVertex k y).val
  · have hb : x.1.val ≠ y.1.val := by
      intro he
      exact hxy (cycleControlVertex_block_injective k x y
        (Fin.ext hc) (Fin.ext he))
    rcases lt_or_gt_of_ne hb with hlt | hgt
    · exact Or.inl (Or.inr ⟨hc,hlt⟩)
    · exact Or.inr (Or.inr ⟨hc.symm,hgt⟩)
  · rcases lt_or_gt_of_ne hc with hlt | hgt
    · exact Or.inl (Or.inl hlt)
    · exact Or.inr (Or.inl hgt)

/-- The explicit total K-completion candidate on the ORIGINAL
finite set of all matched vertices of Ck. -/
def cycleWeakCandidate (k : ℕ) (S : Finset (CycleVertex k)) :
    RelStructure Lang (CycleVertex k) where
  rel
    | .lt, t => cycleWeakOrderLess k (t 0) (t 1)
    | .equiv, t => cycleWeakEClass k S (t 0) =
        cycleWeakEClass k S (t 1)
    | .mate, t => cycleMatching k (t 0) (t 1)

/-- The new target is ALWAYS a genuine member of the finite K,
without any size or closure assumption on S. -/
theorem cycleWeakCandidate_mem_K (k : ℕ)
    (S : Finset (CycleVertex k)) :
    finitePairedClass (cycleWeakCandidate k S) := by
  refine ⟨inferInstance, ?_⟩
  constructor
  · exact cycleWeakOrderLess_irrefl k
  · exact cycleWeakOrderLess_trans k
  · exact cycleWeakOrderLess_total k
  · constructor
    · intro x
      rfl
    · intro x y h
      exact h.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz
  · intro x h
    change cycleMatching k x x at h
    exact h.2 rfl
  · intro x y h
    change cycleMatching k x y at h
    exact ⟨h.1.symm, h.2.symm⟩
  · intro x
    exact cycleMatching_total k x
  · intro x y h
    change cycleMatching k x y at h
    change cycleWeakEClass k S x = cycleWeakEClass k S y
    have hBlock : x.1 = y.1 := h.1
    cases x with
    | mk a i =>
        cases y with
        | mk b j =>
            change a = b at hBlock
            subst b
            rfl

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
