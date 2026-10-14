import AllThoseRamseyClasses.Published.OrderedCompatibleKeys
import AllThoseRamseyClasses.Published.OrderedPushoutFromKeys

/-!
# Common-root order extension for arbitrary finite ordered structures

The existing paired-equivalence implementation proves the root-cut key
construction under the MUCH STRONGER `pairedClass` hypothesis.
Only strict transitivity, irreflexivity, and totality of the distinguished
order are actually used. In particular, no matching and no equivalence
axioms are relevant. We prove that the SAME keys work for arbitrary
members of the 2019 ordered ambient class, and use the already
verified free-amalgam compatible-key assembly.

This constructs a total linear order on the strong *vertex pushout*
extending the exact old orders, without identifying any additional
vertices. It does NOT claim to construct the new transitive partial-
order relation, its induced reflection, or the complete strong
amalgam of ordered posets. These are independent application steps.
-/

namespace AllThoseRamseyClasses.Applications.OrderedPosets

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- The old preorder-rank proof only uses strict order laws.
No matching predicate, E-equivalence, or convexity is required. -/
theorem ambient_sideOrderRank_strictMono
    {X : Type} [Fintype X]
    (Side : RelStructure Lang X) (hSide : orderedAmbientClass Side)
    {x y : X} (hxy : edge Side .lt x y) :
    sideOrderRank Side x < sideOrderRank Side y := by
  classical
  unfold sideOrderRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  refine ⟨x, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hSide.2.1 x
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_filter,
      Finset.mem_univ, true_and] at hz ⊢
    rcases hz with rfl | hzx
    · exact hxy
    · exact hSide.2.2.1 z x y hzx hxy

/-- Common-root cut ranks are monotone for ANY strictly transitive
named order, with no algebraic structure on the other symbols. -/
theorem ambient_rootCut_mono
    {D X : Type} [Fintype D]
    {Root : RelStructure Lang D} {Side : RelStructure Lang X}
    (hSide : orderedAmbientClass Side)
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
  exact ⟨Finset.mem_univ _,
    hSide.2.2.1 (s d) x y hdlt hxy⟩

/-- A common-root point strictly before y is counted in y's cut. -/
theorem ambient_rootCut_strict_after_root
    {D X : Type} [Fintype D]
    {Root : RelStructure Lang D} {Side : RelStructure Lang X}
    (hSide : orderedAmbientClass Side)
    (s : Embedding Root Side) (d : D) (x : X)
    (h : edge Side .lt (s d) x) :
    rootCut Side s (s d) < rootCut Side s x := by
  classical
  unfold rootCut
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  refine ⟨d, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hSide.2.1 (s d)
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_filter,
      Finset.mem_univ, true_and] at hz ⊢
    rcases hz with rfl | hzd
    · exact h
    · exact hSide.2.2.1 (s z) (s d) x hzd h

/-- A private/root lexicographic key respects an arbitrary ambient
linear order: only strict-order axioms and a full root embedding
enter the proof, not `pairedClass`. -/
theorem ambient_sideOrderKey_strictMono
    {D X : Type} [Fintype D] [Fintype X]
    {Root : RelStructure Lang D}
    (Side : RelStructure Lang X) (hSide : orderedAmbientClass Side)
    (s : Embedding Root Side) (privatePriority : ℕ)
    (hPriority : privatePriority < 2)
    {x y : X} (hxy : edge Side .lt x y) :
    sideOrderKey Side s privatePriority x <
      sideOrderKey Side s privatePriority y := by
  classical
  have hCutLe : rootCut Side s x ≤ rootCut Side s y :=
    ambient_rootCut_mono hSide s hxy
  by_cases hCutLt : rootCut Side s x < rootCut Side s y
  · unfold sideOrderKey
    split_ifs <;>
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hCutLt)
  · have hEq : rootCut Side s x = rootCut Side s y := by
      omega
    by_cases hRootX : ∃ d : D, s d = x
    · obtain ⟨d, hd⟩ := hRootX
      have hStrict : rootCut Side s (s d) < rootCut Side s y :=
        ambient_rootCut_strict_after_root hSide s d y
          (by simpa [hd] using hxy)
      rw [hd] at hStrict
      omega
    · by_cases hRootY : ∃ d : D, s d = y
      · have hLex : toLex
            (rootCut Side s x,
              toLex (privatePriority, sideOrderRank Side x)) <
            toLex
            (rootCut Side s y, toLex (2, rootCut Side s y)) :=
          Prod.Lex.toLex_lt_toLex.mpr
            (Or.inr ⟨hEq,
              Prod.Lex.toLex_lt_toLex.mpr (Or.inl hPriority)⟩)
        simpa only [sideOrderKey, dif_neg hRootX,
          dif_pos hRootY] using hLex
      · have hRank : sideOrderRank Side x < sideOrderRank Side y :=
          ambient_sideOrderRank_strictMono Side hSide hxy
        have hLex : toLex
            (rootCut Side s x,
              toLex (privatePriority, sideOrderRank Side x)) <
            toLex
              (rootCut Side s y,
                toLex (privatePriority, sideOrderRank Side y)) :=
          Prod.Lex.toLex_lt_toLex.mpr
            (Or.inr ⟨hEq,
              Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hRank⟩)⟩)
        simpa only [sideOrderKey, dif_neg hRootX,
          dif_neg hRootY] using hLex

/-- Every strong free vertex amalgam of TWO arbitrary finite
ambient ordered structures admits a single order extending both
side orders. There is no extra convexity or order compatibility
assumption, beyond their common full ordered root. -/
theorem ambient_ordered_pushout_exists
    {D E F P : Type}
    [Finite D] [Finite E] [Finite F] [Finite P]
    {Root : RelStructure Lang D}
    {Left : RelStructure Lang E} {Right : RelStructure Lang F}
    {Whole : RelStructure Lang P}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hLeft : orderedAmbientClass Left)
    (hRight : orderedAmbientClass Right) :
    ∃ (o : LinearOrder P),
      (∀ a b : E, edge Left .lt a b →
        @LT.lt P o.toLT (iL a) (iL b)) ∧
      (∀ a b : F, edge Right .lt a b →
        @LT.lt P o.toLT (iR a) (iR b)) := by
  classical
  letI : Fintype D := Fintype.ofFinite D
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype F := Fintype.ofFinite F
  let keyL : E → ℕ ×ₗ (ℕ ×ₗ ℕ) :=
    sideOrderKey Left sL 0
  let keyR : F → ℕ ×ₗ (ℕ ×ₗ ℕ) :=
    sideOrderKey Right sR 1
  have hCompat : ∀ d, keyL (sL d) = keyR (sR d) :=
    sideOrderKey_root_agree sL sR
  have hLtL : ∀ a b : E, edge Left .lt a b →
      keyL a < keyL b := by
    intro a b hab
    exact ambient_sideOrderKey_strictMono Left hLeft sL 0
      (by omega) hab
  have hLtR : ∀ a b : F, edge Right .lt a b →
      keyR a < keyR b := by
    intro a b hab
    exact ambient_sideOrderKey_strictMono Right hRight sR 1
      (by omega) hab
  exact AllThoseRamseyClasses.Published.PairedEquivalenceObstruction.IsFreeAmalgam.exists_order_from_compatible_keys
    hFree keyL keyR hCompat hLtL hLtR

end AllThoseRamseyClasses.Applications.OrderedPosets
