import AllThoseRamseyClasses.Lifts.FiniteAmalgamLeftOrder

/-!
# Track E: exact strong overlap makes the finite lex order extend BOTH sides

The left side of the finite lex amalgam is always preserved
under an order-preserving root injection and an injective left
placement. The RIGHT side is subtler: a right-private target
vertex could be incorrectly classified as a left vertex
unless the side images overlap EXACTLY on the common root.

Using the actual strong-overlap law, the right-side order
is also strictly preserved. This requires no freeness or
strong class structure, only finite linear orders, injective
placements, and the genuine exact strong overlap equivalence.

The final theorem produces one finite target linear order
extending both ordered sides simultaneously. The native
relations, folded predicates and complete set-valued
function output fibres are not altered. This is the
pure finite-order bridge from unordered strong AP to
ordered strong AP, not the finite-family Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey

/-- The explicit finite target order extends the ordered RIGHT
side under the exact strong-overlap law of the two placements.
Unlike the left-side theorem, the strong overlap is essential
for correct right-private classification. -/
theorem finiteAmalgamLinearOrder_right_strictMono
    {X Y Z T : Type}
    [Fintype X] [LinearOrder X]
    [Fintype Y] [LinearOrder Y]
    [Fintype Z] [LinearOrder Z]
    [Fintype T]
    (sY : X → Y) (sZ : X → Z)
    (jY : Y → T) (jZ : Z → T)
    (hsY : StrictMono sY)
    (hsZ : StrictMono sZ)
    (hjY : Function.Injective jY)
    (hjZ : Function.Injective jZ)
    (hOverlap : ∀ y : Y, ∀ z : Z,
      jY y = jZ z ↔
        ∃ x : X, y = sY x ∧ z = sZ x)
    (a b : Z) (hab : a < b) :
    @LT.lt T (finiteAmalgamLinearOrder sY sZ jY jZ).toLT
      (jZ a) (jZ b) := by
  classical
  have hCommon (x : X) :
      jY (sY x) = jZ (sZ x) :=
    (hOverlap (sY x) (sZ x)).mpr
      ⟨x, rfl, rfl⟩
  have hRootKey (x : X) :
      finiteAmalgamOrderKey sY sZ jY jZ (jZ (sZ x)) =
        toLex (StructuralRamsey.Rooted.orderRank X x,
          toLex ((2 : ℕ),
            toLex ((0 : ℕ), Fintype.equivFin T (jZ (sZ x))))) := by
    rw [← hCommon x]
    exact finiteAmalgamOrderKey_on_root
      sY sZ jY jZ hsY.injective hjY x
  change finiteAmalgamOrderKey sY sZ jY jZ (jZ a) <
    finiteAmalgamOrderKey sY sZ jY jZ (jZ b)
  by_cases ha : ∃ x : X, sZ x = a
  · obtain ⟨x, rfl⟩ := ha
    by_cases hb : ∃ x : X, sZ x = b
    · obtain ⟨y, rfl⟩ := hb
      rw [hRootKey x, hRootKey y]
      apply Prod.Lex.toLex_lt_toLex.mpr
      left
      exact (StructuralRamsey.Rooted.orderRank_strictMono X)
        ((hsZ.lt_iff_lt).mp hab)
    · rw [hRootKey x,
        finiteAmalgamOrderKey_on_Z_private
          sY sZ jY jZ hjZ hOverlap b hb]
      apply Prod.Lex.toLex_lt_toLex.mpr
      left
      exact finiteRootCutRank_gt_rootRank_of_above
        sZ hsZ x b hab
  · by_cases hb : ∃ x : X, sZ x = b
    · obtain ⟨y, rfl⟩ := hb
      rw [finiteAmalgamOrderKey_on_Z_private
        sY sZ jY jZ hjZ hOverlap a ha,
        hRootKey y]
      have hle : finiteRootCutRank sZ a ≤
          StructuralRamsey.Rooted.orderRank X y :=
        finiteRootCutRank_le_rootRank_of_below
          sZ hsZ y a hab
      by_cases hlt : finiteRootCutRank sZ a <
          StructuralRamsey.Rooted.orderRank X y
      · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)
      · have heq : finiteRootCutRank sZ a =
            StructuralRamsey.Rooted.orderRank X y :=
          le_antisymm hle (le_of_not_gt hlt)
        apply Prod.Lex.toLex_lt_toLex.mpr
        refine Or.inr ⟨heq, ?_⟩
        apply Prod.Lex.toLex_lt_toLex.mpr
        exact Or.inl (by decide : (1 : ℕ) < 2)
    · rw [finiteAmalgamOrderKey_on_Z_private
        sY sZ jY jZ hjZ hOverlap a ha,
        finiteAmalgamOrderKey_on_Z_private
          sY sZ jY jZ hjZ hOverlap b hb]
      have hle : finiteRootCutRank sZ a ≤
          finiteRootCutRank sZ b :=
        finiteRootCutRank_mono sZ (le_of_lt hab)
      by_cases hlt : finiteRootCutRank sZ a <
          finiteRootCutRank sZ b
      · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)
      · have heq : finiteRootCutRank sZ a =
            finiteRootCutRank sZ b :=
          le_antisymm hle (le_of_not_gt hlt)
        apply Prod.Lex.toLex_lt_toLex.mpr
        refine Or.inr ⟨heq, ?_⟩
        apply Prod.Lex.toLex_lt_toLex.mpr
        refine Or.inr ⟨rfl, ?_⟩
        apply Prod.Lex.toLex_lt_toLex.mpr
        exact Or.inl
          ((StructuralRamsey.Rooted.orderRank_strictMono Z) hab)

/-- Pure order-theoretic strong-amalgamation extension.

If finite ordered sides Y,Z embed injectively in a finite
target T with their images overlapping EXACTLY on one ordered
common root X, the target admits one linear order making
BOTH side embeddings strictly increasing.

The explicit order is the same certified lexicographic key
from earlier Track E branches; no independent order
extension oracle is postulated. -/
theorem exists_finiteAmalgamLinearOrder_extending_both
    {X Y Z T : Type}
    [Fintype X] [LinearOrder X]
    [Fintype Y] [LinearOrder Y]
    [Fintype Z] [LinearOrder Z]
    [Fintype T]
    (sY : X → Y) (sZ : X → Z)
    (jY : Y → T) (jZ : Z → T)
    (hsY : StrictMono sY)
    (hsZ : StrictMono sZ)
    (hjY : Function.Injective jY)
    (hjZ : Function.Injective jZ)
    (hOverlap : ∀ y : Y, ∀ z : Z,
      jY y = jZ z ↔
        ∃ x : X, y = sY x ∧ z = sZ x) :
    ∃ (o : LinearOrder T),
      (∀ a b : Y, a < b →
        @LT.lt T o.toLT (jY a) (jY b)) ∧
      (∀ a b : Z, a < b →
        @LT.lt T o.toLT (jZ a) (jZ b)) := by
  let o := finiteAmalgamLinearOrder sY sZ jY jZ
  refine ⟨o, ?_, ?_⟩
  · intro a b hab
    exact finiteAmalgamLinearOrder_left_strictMono
      sY sZ jY jZ hsY hjY a b hab
  · intro a b hab
    exact finiteAmalgamLinearOrder_right_strictMono
      sY sZ jY jZ hsY hsZ hjY hjZ hOverlap a b hab

end AllThoseRamseyClasses.Lifts
