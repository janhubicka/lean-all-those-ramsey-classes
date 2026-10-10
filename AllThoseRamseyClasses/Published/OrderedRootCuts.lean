import AllThoseRamseyClasses.Published.OrderedAmbientRamsey
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Root-interval cuts for a strong amalgam of linearly ordered sides

The finite root D embeds into two strict-linearly ordered sides.
For each side vertex x, count root vertices preceding x. This count
is the (k+1)-interval index in the elementary amalgamation proof.

The key properties are: interval indices are monotone with the
side order, and the two side embeddings assign identical interval
indices to corresponding root vertices. No convexity of E-classes
or closure of order intervals is assumed.

Completing a strict order on the strong vertex pushout by
lexicographic (interval, side, within-side rank) keys is the next
step. This module is deliberately a small checked building block.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The number of root vertices preceding x in a side linear order. -/
noncomputable def rootCut
    {D X : Type} [Fintype D]
    {Root : RelStructure Lang D}
    (Side : RelStructure Lang X)
    (s : Embedding Root Side) (x : X) : ℕ := by
  classical
  exact ((Finset.univ : Finset D).filter
    (fun d => edge Side .lt (s d) x)).card

/-- A full embedding of ordered relational structures preserves
the order predicate in BOTH directions on every pair. -/
theorem strictOrder_embedding_iff
    {D X : Type}
    {Root : RelStructure Lang D} {Side : RelStructure Lang X}
    (s : Embedding Root Side) (a b : D) :
    edge Side .lt (s a) (s b) ↔ edge Root .lt a b := by
  have htuple : s ∘ ![a, b] = ![s a, s b] := by
    funext i
    fin_cases i <;> rfl
  change Side.rel .lt ![s a, s b] ↔ Root.rel .lt ![a, b]
  rw [← htuple]
  exact s.map_rel_iff .lt ![a, b]

/-- If x precedes y in a side, no root vertex counted before x
can disappear from the list of roots preceding y. -/
theorem rootCut_mono
    {D X : Type} [Fintype D]
    {Root : RelStructure Lang D} {Side : RelStructure Lang X}
    (hSide : pairedClass Side)
    (s : Embedding Root Side)
    {x y : X} (hxy : edge Side .lt x y) :
    rootCut Side s x ≤ rootCut Side s y := by
  classical
  unfold rootCut
  apply Finset.card_le_card
  intro d hd
  have hdlt : edge Side .lt (s d) x :=
    (Finset.mem_filter.mp hd).2
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, hSide.lt_trans (s d) x y hdlt hxy⟩

/-- The two embeddings of the common root agree exactly about
how many root vertices are strictly below each root vertex.
This fixes the interval position of every identified vertex. -/
theorem rootCut_agree_on_root
    {D E F : Type} [Fintype D]
    {Root : RelStructure Lang D}
    {Left : RelStructure Lang E} {Right : RelStructure Lang F}
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (d : D) :
    rootCut Left sL (sL d) = rootCut Right sR (sR d) := by
  classical
  unfold rootCut
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (strictOrder_embedding_iff sL z d).trans
    (strictOrder_embedding_iff sR z d).symm

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
