import AllThoseRamseyClasses.Lifts.Claim2OriginalMinimizerSelectedQChainGates
import AllThoseRamseyClasses.Lifts.Claim2SelectedOuterStrictGlobalB

/-!
# Track B: strict TOTAL B-exclusive source rank along literal selected-Q chains

A full native selected-Q geometric step strictly decreases local
B-exclusive SOURCE count inside its actual new outer piece while
preserving exact SOURCE counts OUTSIDE for EVERY target region.
Consequently it strictly decreases the TOTAL number of B-exclusive
SOURCE vertices in the entire forbidden source.

The underlying finite source-partition lemma is already verified
in Claim2SelectedOuterStrictGlobalB. Here we instantiate it with
the stronger Claim2NativeSelectedQProvenanceStep relation, so each
step of the finite chain remembers its actual forbidden selected Q
and full Q+old-E free-amalgam diagram.

The original left-exclusive A-source support may INCREASE in a B→A
step. This theorem therefore does not justify lexicographic (A,B)
minimality without an independent A-neutrality condition. It
does not remove the original root/boundary source-test gaps or
smaller-root capture/A-mixedness.
-/

namespace AllThoseRamseyClasses.Lifts
open StructuralRamsey
open StructuralRamsey.Structure
universe u
variable {L : Language.{u}}

/-- Literal total right-exclusive SOURCE support (never cardinality
of weak target-map images), across an arbitrary finite native
forbidden source carrier type. -/
noncomputable def claim2NativeTotalBSourceCount
    {F : ∀ {W : Type}, Structure L W → Prop}
    {UX UA UB UT : Type}
    {Target : Structure L UT}
    {Left : Structure L UA} {Right : Structure L UB}
    {jLeft : Structure.Embedding Left Target}
    {jRight : Structure.Embedding Right Target}
    {X : Structure L UX}
    {iLeft : Structure.Embedding X Left}
    {iRight : Structure.Embedding X Right}
    {n : ℕ}
    (s : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n) : ℕ :=
  Nat.card {v : s.Carrier //
    s.f v ∈ fullFreeRightExclusiveTarget iRight jRight}

/-- Each actual selected-Q native source replacement STRICTLY reduces
TOTAL B-exclusive SOURCE count, not merely the local B-rank.
This is implied by its real local rank decrease and exact external
source counts for the B-exclusive target region. -/
theorem claim2NativeSelectedQStep_strictGlobalBSourceCount
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    {n : ℕ} (hn : 0 < n)
    (s t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (hSelectedQ :
      claim2NativeSelectedQProvenanceStep F Target Left Right
        jLeft jRight X iLeft iRight hn s t) :
    claim2NativeTotalBSourceCount t < claim2NativeTotalBSourceCount s := by
  change
    Nat.card {w : t.Carrier //
      t.f w ∈ fullFreeRightExclusiveTarget iRight jRight} <
    Nat.card {v : s.Carrier //
      s.f v ∈ fullFreeRightExclusiveTarget iRight jRight}
  exact finiteSource_strict_global_active_of_inside_and_exterior
    s.finite t.finite
    (geometricPieceVertices s.source s.outer)
    (geometricPieceVertices t.source t.outer)
    s.f t.f (fullFreeRightExclusiveTarget iRight jRight)
    hSelectedQ.1.2.2.1
    (hSelectedQ.1.2.2.2.1
      (fullFreeRightExclusiveTarget iRight jRight))

/-- A FINITE chain of source replacements with a literal selected
forbidden Q and its complete native E complement on EVERY edge
has an exact TOTAL B-exclusive source-support budget:
    length + totalB(terminal) ≤ totalB(initial).

The local-rank budget of Claim2SelectedQStateProvenance remains
separately available and is often sharper. This theorem gives the
global bound needed when considering a secondary B-minimal
forbidden SOURCE witness. -/
theorem claim2NativeSelectedQChain_globalBSourceBudget
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    {n : ℕ} (hn : 0 < n)
    {k : ℕ}
    {s t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n}
    (hChain : ConditionalSelectedQChain
      (claim2NativeSelectedQProvenanceStep F Target Left Right
        jLeft jRight X iLeft iRight hn) k s t) :
    k + claim2NativeTotalBSourceCount t ≤
      claim2NativeTotalBSourceCount s := by
  have hDecrease :
      ∀ ⦃a b : Claim2NativeGeometricState F Target Left Right
          jLeft jRight X iLeft iRight n⦄,
        claim2NativeSelectedQProvenanceStep F Target Left Right
          jLeft jRight X iLeft iRight hn a b →
        claim2NativeTotalBSourceCount b <
          claim2NativeTotalBSourceCount a := by
    intro a b hStep
    exact claim2NativeSelectedQStep_strictGlobalBSourceCount
      F Target Left Right jLeft jRight
      X iLeft iRight hn a b hStep
  exact conditionalSelectedQChain_rank_budget
    claim2NativeTotalBSourceCount hDecrease hChain

end AllThoseRamseyClasses.Lifts
