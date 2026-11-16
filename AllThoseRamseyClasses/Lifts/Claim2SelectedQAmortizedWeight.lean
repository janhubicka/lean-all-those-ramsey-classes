import AllThoseRamseyClasses.Lifts.Claim2AFreeQPrivateCostTelescope
import Mathlib.Tactic

/-!
# Track B: a valid conditional amortized potential for selected-Q source descent

The literal same selected forbidden Q+old-E free diagram stores:
  total A(new) = total A(old) + private A(Q)
  total B(new) < total B(old).

Because private A(Q) need not vanish, minimizing original A
(or lexicographically minimizing (A,B)) is NOT automatically
preserved along these one-sided B->A native source replacements.

A different possible termination measure is
  Phi_W(s) := A_total(s) + W * B_total(s).
If the actual private Q-nonroot A-SOURCE cost at EVERY chosen step
is STRICTLY BELOW W, then Phi_W decreases by at least one,
even when A grows. Hence an actual costed Q-chain of length k has
  k + Phi_W(terminal) <= Phi_W(initial).

The cost bound is an EXPLICIT assumption here, not inferred from
mere finiteness of each forbidden source or from original global
canonical lifts. A genuine uniform size bound on forbidden
source pieces may eventually imply it. Nor does the potential
remove old-root capture/A-mixedness or normalize initial weak EHN
source collisions. This is a valid conditional arithmetic API,
not a completed unrestricted original 2019 Claim 2 proof.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Weighted SOURCE support of one genuine native forbidden
EHN map. Neither term counts the weak target-map IMAGE;
both count distinct literal SOURCE vertices. -/
noncomputable def claim2NativeWeightedABSourcePotential
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
    (weight : ℕ)
    (s : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n) : ℕ :=
  claim2NativeTotalASourceCount s +
    weight * claim2NativeTotalBSourceCount s

/-- One literal A-free selected-Q native source replacement has
STRICTLY SMALLER weighted SOURCE support whenever its EXACT
private-Q A-exclusive SOURCE cardinality is less than weight.

The proof uses original exact E/Q source-cardinality accounting
and global B-SOURCE loss; it never assumes A-neutrality. -/
theorem claim2NativeAFreeQCostedStep_strictWeightedPotential
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
    (weight : ℕ)
    (s t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (privateACost : ℕ)
    (hStep : claim2NativeAFreeQStepWithPrivateCost F Target Left Right
      jLeft jRight X iLeft iRight hn s t privateACost)
    (hCostBound : privateACost < weight) :
    claim2NativeWeightedABSourcePotential weight t <
      claim2NativeWeightedABSourcePotential weight s := by
  have hAExact :=
    claim2NativeAFreeQStepWithPrivateCost_exactTotalA
      F Target Left Right jLeft jRight X iLeft iRight
      hn s t privateACost hStep
  have hAFree : claim2NativeAFreeSelectedQStep F Target Left Right
      jLeft jRight X iLeft iRight hn s t :=
    claim2NativeAFreeQStepWithPrivateCost.toAFreeStep
      F Target Left Right jLeft jRight X iLeft iRight
      hn s t privateACost hStep
  have hSelected : claim2NativeSelectedQProvenanceStep F Target
      Left Right jLeft jRight X iLeft iRight hn s t :=
    claim2NativeAFreeSelectedQStep.toSelectedQProvenance
      F Target Left Right jLeft jRight X iLeft iRight
      hn s t hAFree
  have hBStrict :
      claim2NativeTotalBSourceCount t <
        claim2NativeTotalBSourceCount s :=
    claim2NativeSelectedQStep_strictGlobalBSourceCount
      F Target Left Right jLeft jRight X iLeft iRight
      hn s t hSelected
  have hBSucc : claim2NativeTotalBSourceCount t + 1 ≤
      claim2NativeTotalBSourceCount s := Nat.succ_le_of_lt hBStrict
  have hMul :
      weight * claim2NativeTotalBSourceCount t + weight ≤
      weight * claim2NativeTotalBSourceCount s := by
    simpa only [Nat.mul_add, Nat.mul_one] using
      (Nat.mul_le_mul_left weight hBSucc)
  dsimp [claim2NativeWeightedABSourcePotential]
  omega

/-- Any finite chain of real A-free Q+E native source replacements,
with the exact private Q A-SOURCE cost recorded on EACH edge,
strictly decreases the weighted support at EVERY transition
when all private costs are below one fixed positive weight.

The cumulative potential drop pays for the entire chain length.
This is a conditional well-foundedness theorem, not a guarantee
of arbitrary next-step Q eligibility or obstruction removal. -/
theorem claim2NativeAFreeQCostedChain_weightedBudget
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
    (weight : ℕ)
    {k totalPrivateCost : ℕ}
    {s t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n}
    (hChain : Claim2NativeAFreeQCostedChain F Target Left Right
      jLeft jRight X iLeft iRight hn k s t totalPrivateCost)
    (hAllCostsBelowWeight :
      ∀ ⦃a b : Claim2NativeGeometricState F Target Left Right
          jLeft jRight X iLeft iRight n⦄ ⦃cost : ℕ⦄,
        claim2NativeAFreeQStepWithPrivateCost F Target Left Right
          jLeft jRight X iLeft iRight hn a b cost →
        cost < weight) :
    k + claim2NativeWeightedABSourcePotential weight t ≤
      claim2NativeWeightedABSourcePotential weight s := by
  have hOne :
      ∀ ⦃a b : Claim2NativeGeometricState F Target Left Right
          jLeft jRight X iLeft iRight n⦄ ⦃cost : ℕ⦄,
        claim2NativeAFreeQStepWithPrivateCost F Target Left Right
          jLeft jRight X iLeft iRight hn a b cost →
        claim2NativeWeightedABSourcePotential weight b <
          claim2NativeWeightedABSourcePotential weight a := by
    intro a b cost hStep
    exact claim2NativeAFreeQCostedStep_strictWeightedPotential
      F Target Left Right jLeft jRight X iLeft iRight
      hn weight a b cost hStep (hAllCostsBelowWeight hStep)
  induction hChain with
  | nil s =>
      omega
  | cons hStep hTail ih =>
      have hStrict := hOne hStep
      omega

end AllThoseRamseyClasses.Lifts
