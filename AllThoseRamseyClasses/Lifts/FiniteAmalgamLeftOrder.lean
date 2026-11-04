import AllThoseRamseyClasses.Lifts.FiniteAmalgamOrderKeyEvaluation

/-!
# Track E: the finite amalgam lex order genuinely extends the LEFT order

The verified four-coordinate lex order on an arbitrary finite
strong-amalgamation target classifies a target vertex by its
common-root cut and whether it is a shared-root, left-private,
right-private, or target-extra vertex.

The LEFT side is special: its target image is categorized by
the common-root branch or the left-private branch, even if the
other side overlaps spuriously. Therefore strict monotonicity
of the left embedding in the new target order needs ONLY:
* the common root-to-left map is strictly increasing;
* the left-to-target map is injective.

No strong overlap law, right-side monotonicity or target
free-amalgamation assumption is necessary for this lemma.

We check all four combinations of root/private vertices
on the left, including the crucial private-before-root case
with equal root cut: category zero precedes root category two.
This is the first actual extension theorem for the ordered
strong-amalgamation bridge; the right side will need the exact
strong-overlap law to exclude false left-side classification.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey

/-- The explicit finite lexicographic order ALWAYS extends the
prescribed left-side order, provided the common-root embedding
is strictly increasing and the left side is injectively placed
in the target. This holds with arbitrary right-side map,
including one that violates strong amalgamation.

No constraints on native relation or function arities are used. -/
theorem finiteAmalgamLinearOrder_left_strictMono
    {X Y Z T : Type}
    [Fintype X] [LinearOrder X]
    [Fintype Y] [LinearOrder Y]
    [Fintype Z] [LinearOrder Z]
    [Fintype T]
    (sY : X → Y) (sZ : X → Z)
    (jY : Y → T) (jZ : Z → T)
    (hsY : StrictMono sY)
    (hjY : Function.Injective jY)
    (a b : Y) (hab : a < b) :
    @LT.lt T (finiteAmalgamLinearOrder sY sZ jY jZ).toLT
      (jY a) (jY b) := by
  classical
  change finiteAmalgamOrderKey sY sZ jY jZ (jY a) <
    finiteAmalgamOrderKey sY sZ jY jZ (jY b)
  by_cases ha : ∃ x : X, sY x = a
  · obtain ⟨x, rfl⟩ := ha
    by_cases hb : ∃ x : X, sY x = b
    · obtain ⟨y, rfl⟩ := hb
      rw [finiteAmalgamOrderKey_on_root sY sZ jY jZ
        hsY.injective hjY x,
        finiteAmalgamOrderKey_on_root sY sZ jY jZ
          hsY.injective hjY y]
      apply Prod.Lex.toLex_lt_toLex.mpr
      left
      exact (StructuralRamsey.Rooted.orderRank_strictMono X)
        ((hsY.lt_iff_lt).mp hab)
    · rw [finiteAmalgamOrderKey_on_root sY sZ jY jZ
        hsY.injective hjY x,
        finiteAmalgamOrderKey_on_Y_private sY sZ jY jZ
          hjY b hb]
      apply Prod.Lex.toLex_lt_toLex.mpr
      left
      exact finiteRootCutRank_gt_rootRank_of_above
        sY hsY x b hab
  · by_cases hb : ∃ x : X, sY x = b
    · obtain ⟨y, rfl⟩ := hb
      rw [finiteAmalgamOrderKey_on_Y_private sY sZ jY jZ
        hjY a ha,
        finiteAmalgamOrderKey_on_root sY sZ jY jZ
          hsY.injective hjY y]
      have hle : finiteRootCutRank sY a ≤
          StructuralRamsey.Rooted.orderRank X y :=
        finiteRootCutRank_le_rootRank_of_below
          sY hsY y a hab
      by_cases hlt : finiteRootCutRank sY a <
          StructuralRamsey.Rooted.orderRank X y
      · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)
      · have heq : finiteRootCutRank sY a =
            StructuralRamsey.Rooted.orderRank X y :=
          le_antisymm hle (le_of_not_gt hlt)
        apply Prod.Lex.toLex_lt_toLex.mpr
        refine Or.inr ⟨heq, ?_⟩
        apply Prod.Lex.toLex_lt_toLex.mpr
        exact Or.inl (by decide : (0 : ℕ) < 2)
    · rw [finiteAmalgamOrderKey_on_Y_private sY sZ jY jZ
        hjY a ha,
        finiteAmalgamOrderKey_on_Y_private sY sZ jY jZ
          hjY b hb]
      have hle : finiteRootCutRank sY a ≤
          finiteRootCutRank sY b :=
        finiteRootCutRank_mono sY (le_of_lt hab)
      by_cases hlt : finiteRootCutRank sY a <
          finiteRootCutRank sY b
      · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)
      · have heq : finiteRootCutRank sY a =
            finiteRootCutRank sY b :=
          le_antisymm hle (le_of_not_gt hlt)
        apply Prod.Lex.toLex_lt_toLex.mpr
        refine Or.inr ⟨heq, ?_⟩
        apply Prod.Lex.toLex_lt_toLex.mpr
        refine Or.inr ⟨rfl, ?_⟩
        apply Prod.Lex.toLex_lt_toLex.mpr
        exact Or.inl
          ((StructuralRamsey.Rooted.orderRank_strictMono Y) hab)

end AllThoseRamseyClasses.Lifts
