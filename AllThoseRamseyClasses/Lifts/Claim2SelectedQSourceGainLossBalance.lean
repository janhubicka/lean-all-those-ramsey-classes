import AllThoseRamseyClasses.Lifts.Claim2SelectedQAactiveSourceCost

/-!
# Exact SOURCE support gain/loss balance under a selected-Q flip

For ANY target support region Active, a genuine old native source
has its Active source vertices partitioned into the retained full
complement E and the selected old nonroot component C.
The ACTUAL new full Q+_R E free-amalgam source has its Active
source vertices partitioned into E and the newly inserted
private Q nonroot source vertices. The old/new target values
on E agree exactly.

On finite old/new genuine source carriers, this gives the
exact natural-number accounting identity:

  NEW Active SOURCE count + OLD deleted-component Active count
    = OLD Active SOURCE count + NEW private-Q Active count.

This compares ACTUAL source vertices, not target images. It does
not assume the OLD deleted component is A-free, so it also applies
to B-exclusive support. In the special B-to-A flip where Q
contributes NO new B-exclusive vertex, the formula yields
the exact amount of B-source support lost: precisely the old
B-exclusive source count inside the removed component.

The A-side identity instead records the private Q A-support
cost, making the two directions of an attempted lexicographic
or amortized descent explicit.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- For any finite OLD native source, split its Active-SOURCE
vertices exactly into the FULL retained complement E and
the old selected inner nonroot component. The two native
source subsets are disjoint by the literal definition of E. -/
theorem geometricSelectedQ_old_support_card_retained_add_removed
    {V UT : Type}
    (Old : Structure L V) (hFiniteOld : Finite V)
    {m : ℕ} (inner : GeometricFunctionalPieceData Old m)
    (f : V → UT) (Active : Set UT) :
    Nat.card {v : V // f v ∈ Active} =
      Nat.card {e : (geometricGlobalComplementChart Old inner).Carrier //
        f e.1 ∈ Active} +
      Nat.card {v : V //
        v ∈ functionalComponentFrom Old
          (Set.range inner.roots) inner.left ∧
        f v ∈ Active} := by
  classical
  letI : Finite V := hFiniteOld
  let E := geometricGlobalComplementChart Old inner
  let C : Set V :=
    functionalComponentFrom Old (Set.range inner.roots) inner.left
  let iOldE : Structure.Embedding E.str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range inner.roots) inner.minimal.1 inner.left
  let EActive : Set E.Carrier := {e | f e.1 ∈ Active}
  let CActive : Set V := {v | v ∈ C ∧ f v ∈ Active}
  have hPartition :
      {v : V | f v ∈ Active} =
        iOldE '' EActive ∪ CActive := by
    ext v
    constructor
    · intro hvA
      by_cases hvC : v ∈ C
      · exact Or.inr ⟨hvC, hvA⟩
      · exact Or.inl ⟨⟨v, hvC⟩, hvA, rfl⟩
    · intro hv
      rcases hv with ⟨e, heA, rfl⟩ | ⟨_hvC, hvA⟩
      · exact heA
      · exact hvA
  have hDisjoint : Disjoint (iOldE '' EActive) CActive := by
    apply Set.disjoint_left.mpr
    intro v hvE hvC
    obtain ⟨e, _heA, he⟩ := hvE
    have hvNotC : v ∉ C := by
      rw [← he]
      exact e.2
    exact hvNotC hvC.1
  change Nat.card (↑({v : V | f v ∈ Active} : Set V)) =
    Nat.card (↑(EActive : Set E.Carrier)) +
      Nat.card (↑(CActive : Set V))
  simp only [Nat.card_coe_set_eq]
  rw [hPartition, Set.ncard_union_eq hDisjoint,
    Set.ncard_image_of_injective _ iOldE.injective]

/-- Exact gain/loss balance of actual source support in any
FULL native geometric selected-Q replacement with E agreement.
The OLD component need NOT be A-free. All source counts are
genuine Nat.card of finite original/new SOURCE carriers.

This same formula applies to A-exclusive, B-exclusive, or
any other fixed set of target vertices Active. -/
theorem geometricSelectedQ_exact_source_gain_loss_balance
    {V W UT : Type}
    (Old : Structure L V) (hFiniteOld : Finite V)
    {m : ℕ}
    (inner : GeometricFunctionalPieceData Old m)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (New : Structure L W) (hFiniteNew : Finite W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (f : V → UT) (flip : W → UT) (Active : Set UT)
    (hEAgree : ∀ e : (geometricGlobalComplementChart Old inner).Carrier,
      flip (iE e) = f e.1) :
    Nat.card {w : W // flip w ∈ Active} +
      Nat.card {v : V //
        v ∈ functionalComponentFrom Old
          (Set.range inner.roots) inner.left ∧
        f v ∈ Active} =
      Nat.card {v : V // f v ∈ Active} +
      Nat.card {q : Q.Carrier //
        q ∉ Set.range Q.rootEmbedding ∧
        flip (iQ q) ∈ Active} := by
  let retained : ℕ :=
    Nat.card {e : (geometricGlobalComplementChart Old inner).Carrier //
      f e.1 ∈ Active}
  let removed : ℕ :=
    Nat.card {v : V //
      v ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left ∧ f v ∈ Active}
  let inserted : ℕ :=
    Nat.card {q : Q.Carrier //
      q ∉ Set.range Q.rootEmbedding ∧ flip (iQ q) ∈ Active}
  have hOldCount :
      Nat.card {v : V // f v ∈ Active} = retained + removed :=
    geometricSelectedQ_old_support_card_retained_add_removed
      Old hFiniteOld inner f Active
  have hNewCount :
      Nat.card {w : W // flip w ∈ Active} = retained + inserted :=
    geometricSelectedQ_Aactive_support_card_add_retained
      Old inner Q New hFiniteNew iQ iE hNewFree
      f flip Active hEAgree
  calc
    Nat.card {w : W // flip w ∈ Active} + removed =
        (retained + inserted) + removed := by rw [hNewCount]
    _ = (retained + removed) + inserted := by
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = Nat.card {v : V // f v ∈ Active} + inserted := by
      rw [hOldCount]

/-- In an ACTUAL B-to-A selected-Q replacement, when ALL new
Q source vertices avoid the B-active region, the exact amount
of B-active SOURCE support deleted is the old B-active source
count inside the selected old nonroot component.

Unlike the mere strict-rank-drop lemma, this identity records
the entire finite source count with NO target-image quotient. -/
theorem geometricSelectedQ_noNewB_exact_Bsource_loss
    {V W UT : Type}
    (Old : Structure L V) (hFiniteOld : Finite V)
    {m : ℕ}
    (inner : GeometricFunctionalPieceData Old m)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (New : Structure L W) (hFiniteNew : Finite W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (f : V → UT) (flip : W → UT) (BActive : Set UT)
    (hEAgree : ∀ e : (geometricGlobalComplementChart Old inner).Carrier,
      flip (iE e) = f e.1)
    (hNoBFromQ : ∀ q : Q.Carrier, flip (iQ q) ∉ BActive) :
    Nat.card {w : W // flip w ∈ BActive} +
      Nat.card {v : V //
        v ∈ functionalComponentFrom Old
          (Set.range inner.roots) inner.left ∧
        f v ∈ BActive} =
      Nat.card {v : V // f v ∈ BActive} := by
  have hBalance :=
    geometricSelectedQ_exact_source_gain_loss_balance
      Old hFiniteOld inner Q New hFiniteNew
      iQ iE hNewFree f flip BActive hEAgree
  have hPrivateEmpty :
      ({q : Q.Carrier | q ∉ Set.range Q.rootEmbedding ∧
        flip (iQ q) ∈ BActive} : Set Q.Carrier) = ∅ := by
    ext q
    constructor
    · intro hq
      exact (hNoBFromQ q) hq.2
    · intro hq
      exact False.elim (Set.not_mem_empty q hq)
  have hPrivateZero :
      Nat.card {q : Q.Carrier //
        q ∉ Set.range Q.rootEmbedding ∧
        flip (iQ q) ∈ BActive} = 0 := by
    change Nat.card (↑({q : Q.Carrier |
      q ∉ Set.range Q.rootEmbedding ∧
      flip (iQ q) ∈ BActive} : Set Q.Carrier)) = 0
    rw [Nat.card_coe_set_eq, hPrivateEmpty]
    simp
  simpa only [hPrivateZero, Nat.add_zero] using hBalance

/-- A purely numerical exact descent criterion for weighted
source support potentials. If A grows by private Q cost `aCost`
and B decreases by exactly the old removed B count `bLost`,
then the weighted potential `B + weight * A` strictly drops
IF AND ONLY IF the weighted NEW A cost is smaller than the old
B count removed.

No unproved claim that this inequality holds for all selected Q. -/
theorem nat_weightedSupport_descent_iff_privateCost_lt_removed
    (aOld aNew bOld bNew aCost bLost weight : ℕ)
    (hA : aNew = aOld + aCost)
    (hB : bNew + bLost = bOld) :
    bNew + weight * aNew < bOld + weight * aOld ↔
      weight * aCost < bLost := by
  have hBalance :
      (bNew + weight * aNew) + bLost =
        (bOld + weight * aOld) + weight * aCost := by
    calc
      (bNew + weight * aNew) + bLost =
          (bNew + bLost) + weight * aNew := by ac_rfl
      _ = bOld + weight * (aOld + aCost) := by
        rw [hB, hA]
      _ = bOld + (weight * aOld + weight * aCost) := by
        rw [Nat.mul_add]
      _ = (bOld + weight * aOld) + weight * aCost := by
        ac_rfl
  constructor
  · intro hDecrease
    have hAdd :
        (bOld + weight * aOld) + weight * aCost <
          (bOld + weight * aOld) + bLost := by
      calc
        (bOld + weight * aOld) + weight * aCost =
            (bNew + weight * aNew) + bLost := hBalance.symm
        _ < (bOld + weight * aOld) + bLost :=
          Nat.add_lt_add_right hDecrease bLost
    exact Nat.add_lt_add_iff_left.mp hAdd
  · intro hPrivateBound
    have hAdd :
        (bNew + weight * aNew) + bLost <
          (bOld + weight * aOld) + bLost := by
      calc
        (bNew + weight * aNew) + bLost =
            (bOld + weight * aOld) + weight * aCost := hBalance
        _ < (bOld + weight * aOld) + bLost :=
          Nat.add_lt_add_left hPrivateBound _
    exact Nat.add_lt_add_iff_right.mp hAdd

/-- Concrete weighted potential criterion for the SAME genuine
selected-Q native B-to-A source flip of an OLD A-free component.

The weighted potential on actual SOURCE vertices,
  B-source-count + weight * A-source-count,
strictly decreases EXACTLY when the A-active private Q cost,
multiplied by weight, is strictly smaller than the B-active
count of the removed old selected component.

This quantifies the missing numerical condition for any proposed
amortized successor; no existence of such Q or weight is asserted. -/
theorem geometricSelectedQ_weighted_source_descent_iff
    {V W UT : Type}
    (Old : Structure L V) (hFiniteOld : Finite V)
    {m : ℕ}
    (inner : GeometricFunctionalPieceData Old m)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (New : Structure L W) (hFiniteNew : Finite W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (f : V → UT) (flip : W → UT)
    (AActive BActive : Set UT)
    (hEAgree : ∀ e : (geometricGlobalComplementChart Old inner).Carrier,
      flip (iE e) = f e.1)
    (hOldInnerNoA : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left →
      f z ∉ AActive)
    (hNoBFromQ : ∀ q : Q.Carrier, flip (iQ q) ∉ BActive)
    (weight : ℕ) :
    (Nat.card {w : W // flip w ∈ BActive} +
        weight * Nat.card {w : W // flip w ∈ AActive} <
      Nat.card {v : V // f v ∈ BActive} +
        weight * Nat.card {v : V // f v ∈ AActive})
    ↔
    (weight *
        Nat.card {q : Q.Carrier //
          q ∉ Set.range Q.rootEmbedding ∧
          flip (iQ q) ∈ AActive} <
      Nat.card {v : V //
        v ∈ functionalComponentFrom Old
          (Set.range inner.roots) inner.left ∧
        f v ∈ BActive}) := by
  have hA :=
    geometricSelectedQ_AfreeOld_exact_Aactive_cost
      Old inner Q New hFiniteNew iQ iE hNewFree
      f flip AActive hOldInnerNoA hEAgree
  have hB :=
    geometricSelectedQ_noNewB_exact_Bsource_loss
      Old hFiniteOld inner Q New hFiniteNew
      iQ iE hNewFree f flip BActive hEAgree hNoBFromQ
  exact nat_weightedSupport_descent_iff_privateCost_lt_removed
    (Nat.card {v : V // f v ∈ AActive})
    (Nat.card {w : W // flip w ∈ AActive})
    (Nat.card {v : V // f v ∈ BActive})
    (Nat.card {w : W // flip w ∈ BActive})
    (Nat.card {q : Q.Carrier //
      q ∉ Set.range Q.rootEmbedding ∧ flip (iQ q) ∈ AActive})
    (Nat.card {v : V //
      v ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left ∧ f v ∈ BActive})
    weight hA hB

end AllThoseRamseyClasses.Lifts
