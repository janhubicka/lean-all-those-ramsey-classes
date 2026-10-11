import AllThoseRamseyClasses.Published.CoordinatedWeakPairedCompletionTarget
import AllThoseRamseyClasses.Published.CoordinatedGadgetLabelInjectivity

/-!
# Exact order and matching reflection of the weak completion D(k,S)

D(k,S) extends the partial source order to a strict total order
using its C0 control order and the actual matching-block indices
for ties. The tie breaker never changes relations within a single
gadget: C0 is injective on each gadget because its three block labels
are distinct, and its two matched bits project to distinct vertices.

Thus the new total order agrees EXACTLY with the old partial
order on every pair of vertices occurring in some common gadget,
which includes every pair of a protected closed U-irreducible test.
The matching relation is unchanged everywhere and all two
vertices of one matching block remain E-equivalent.

The remaining (4c) obligation is precisely the E-equivalence
reflection across distinct matching blocks in a common gadget.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Equal control values for two gadget-related vertices imply
equality of the entire vertices, not just their matching blocks. -/
theorem cycleControlVertex_injective_of_related (k : ℕ)
    (x y : CycleVertex k)
    (hRelated : cycleRelatedBlocks k x.1 y.1)
    (hc : cycleControlVertex k x = cycleControlVertex k y) :
    x = y := by
  have hb : x.1 = y.1 := by
    rcases hRelated with hab | ⟨g,hx,hy⟩
    · exact hab
    · apply cycleGadget_blockLabel_injective k g x.1 y.1 hx hy
      rcases x with ⟨a,i⟩
      rcases y with ⟨b,j⟩
      have hval := congrArg (fun z : Fin 10 => z.val) hc
      change 2 * cycleBlockLabel k a + i.val =
        2 * cycleBlockLabel k b + j.val at hval
      have hi := i.isLt
      have hj := j.isLt
      omega
  exact cycleControlVertex_block_injective k x y hc hb

/-- The new strict total order agrees with the original partial
order whenever both vertices lie in the support of a common gadget.
No U-closedness or finiteness assumption on the tested S is needed. -/
theorem cycleWeakCandidate_lt_iff_of_related (k : ℕ)
    (S : Finset (CycleVertex k))
    (x y : CycleVertex k)
    (hRelated : cycleRelatedBlocks k x.1 y.1) :
    edge (cycleWeakCandidate k S) .lt x y ↔
      edge (cycleGadgetWitness k) .lt x y := by
  change cycleWeakOrderLess k x y ↔
    (cycleRelatedBlocks k x.1 y.1 ∧
      (cycleControlVertex k x).val < (cycleControlVertex k y).val)
  constructor
  · intro h
    refine ⟨hRelated, ?_⟩
    rcases h with hlt | ⟨hEqual,hBlock⟩
    · exact hlt
    · have hxy : x = y :=
        cycleControlVertex_injective_of_related
          k x y hRelated (Fin.ext hEqual)
      subst y
      exact False.elim (Nat.lt_irrefl _ hBlock)
  · intro h
    exact Or.inl h.2

/-- The K-completion preserves *all* matching tuples, positively
and negatively, even outside installed gadget supports. -/
theorem cycleWeakCandidate_mate_iff (k : ℕ)
    (S : Finset (CycleVertex k)) (x y : CycleVertex k) :
    edge (cycleWeakCandidate k S) .mate x y ↔
      edge (cycleGadgetWitness k) .mate x y :=
  Iff.rfl

/-- E already agrees within each matching block; only the
gadgetwise *cross-block* E reflection remains open. -/
theorem cycleWeakCandidate_E_of_sameBlock (k : ℕ)
    (S : Finset (CycleVertex k)) (x y : CycleVertex k)
    (h : x.1 = y.1) :
    edge (cycleWeakCandidate k S) .equiv x y := by
  change cycleWeakEClass k S x = cycleWeakEClass k S y
  rcases x with ⟨a,i⟩
  rcases y with ⟨b,j⟩
  change a = b at h
  subst b
  rfl

/-- All positive source order and matching tuples survive in the
new target; E-positive preservation will use the distinct component
labels and is intentionally not claimed in this file. -/
theorem cycleWeakCandidate_lt_positive (k : ℕ)
    (S : Finset (CycleVertex k)) (x y : CycleVertex k)
    (h : edge (cycleGadgetWitness k) .lt x y) :
    edge (cycleWeakCandidate k S) .lt x y := by
  exact (cycleWeakCandidate_lt_iff_of_related k S x y h.1).mpr h

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
