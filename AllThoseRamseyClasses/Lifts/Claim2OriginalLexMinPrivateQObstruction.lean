import AllThoseRamseyClasses.Lifts.Claim2AFreeSelectedQChainMonotonicity
import AllThoseRamseyClasses.Lifts.Claim2GlobalLexSourceMinimizer

/-!
# Track B: original lex-minimality forces private-Q A-cost, not A-neutrality

A globally minimum ORIGINAL finite forbidden EHN weak-map source
can be chosen lexicographically in (A-exclusive SOURCE support,
B-exclusive SOURCE support). At positive B-source rank, the genuine
geometric selector produces either an A-free native same-selected-Q
replacement OR two literal smaller-root obstructions.

The stronger native state relation now records the actual old
A-FREE selected component alongside the SAME forbidden replacement
Q, old E complement and full free-amalgam source diagram. The exact
source A-cardinality identity and strictly decreasing TOTAL B-count
show that a successful Q at a globally lex-minimal original witness
MUST introduce positive PRIVATE Q-nonroot A-exclusive SOURCE cost.
It is an invalid shortcut to suppose a canonical Q is A-neutral.

For a nonempty finite such Q-chain starting at a globally lex-minimal
original witness, total A-exclusive SOURCE support is STRICTLY
larger at the end, although total B support has strictly dropped.
No intermediate witness is asserted globally A-minimal.

Both the root/boundary initial collision gate and old-root capture
or A-mixed smaller component remain genuine open cases. This
does not prove unrestricted original 2019 Claim 2/strong AP.
No source image quotient, second Q or frozen manuscript edits.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The obstruction at an ORIGINAL globally lex-minimal native
forbidden weak-map SOURCE and positive local B-exclusive rank:
either an actual one-sided SAME selected Q exists and its
private Q-nonroot A-exclusive SOURCE cardinality is POSITIVE,
or there is a literal old-root capture / A-mixed smaller root.

The positive cost is DERIVED from strict global B-source
decrease and global original (A,B)-lexicographic minimality,
not imposed as a canonical selected-Q hypothesis. -/
theorem claim2Native_originalLexMin_positiveRank_privateQA_or_capture_or_mixed
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    {n : ℕ} (hn : 0 < n)
    (s : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (hPositive : 0 < claim2NativeBSourceRank s)
    (hGlobalAMin :
      ∀ {Z : Type} (Candidate : Structure L Z)
        (hCandidate : F Candidate) (g : Z → UT),
        Candidate.IsEHNHomomorphismEmbedding Target g →
        Nat.card {v : s.Carrier //
          s.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
        Nat.card {z : Z //
          g z ∈ fullFreeLeftExclusiveTarget iLeft jLeft})
    (hBMinAtA :
      ∀ {Z : Type} (Candidate : Structure L Z)
        (hCandidate : F Candidate) (g : Z → UT),
        Candidate.IsEHNHomomorphismEmbedding Target g →
        Nat.card {z : Z //
          g z ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
        Nat.card {v : s.Carrier //
          s.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} →
        Nat.card {v : s.Carrier //
          s.f v ∈ fullFreeRightExclusiveTarget iRight jRight} ≤
        Nat.card {z : Z //
          g z ∈ fullFreeRightExclusiveTarget iRight jRight}) :
    (∃ t : Claim2NativeGeometricState F Target Left Right
        jLeft jRight X iLeft iRight n,
      claim2NativeAFreeSelectedQStep F Target Left Right
        jLeft jRight X iLeft iRight hn s t ∧
      ∃ (m : ℕ) (inner : GeometricFunctionalPieceData s.source m)
        (Q : FunctionalRootExtension
          (geometricGlobalFunctionalChart s.source inner).root)
        (iQ : Structure.Embedding Q.str t.source),
        0 < Nat.card {q : Q.Carrier //
          q ∉ Set.range Q.rootEmbedding ∧
          t.f (iQ q) ∈ fullFreeLeftExclusiveTarget iLeft jLeft}) ∨
      claim2NativeOldRootCapture s ∨
      claim2NativeAMixedRoot s := by
  rcases claim2Native_positiveRank_AFreeQStep_or_capture_or_mixed
      F hFiniteF hConnected Target Left Right
      jLeft jRight X iLeft iRight hFree hCommon
      hn s hPositive with
    ⟨t, hStep⟩ | hCapture | hMixed
  · obtain ⟨m, inner, Q, iQ, hCost⟩ :=
      claim2NativeOriginalLexMin_AFreeSelectedQStep_positivePrivateACost
        F Target Left Right jLeft jRight X iLeft iRight
        hn s t hStep hGlobalAMin hBMinAtA
    exact Or.inl ⟨t, hStep, m, inner, Q, iQ, hCost⟩
  · exact Or.inr (Or.inl hCapture)
  · exact Or.inr (Or.inr hMixed)

/-- A NONEMPTY finite chain of full one-sided source replacements,
each storing its literal selected forbidden Q and old A-freeness,
starting at an ORIGINAL globally (A,B)-lex-minimal witness,
ends with STRICTLY GREATER total A-exclusive SOURCE support.

The chain's strict B-source budget shows the final source has
smaller TOTAL B support than the original. The original global
A-min and B-tie-min properties forbid an A-neutral endpoint.
This does not presume lex-minimality for intermediate states,
nor assert that private Q costs of individual steps vanish. -/
theorem claim2Native_originalLexMin_nonemptyAFreeQChain_strictTotalAGrowth
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
    (initial terminal : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (hChain : ConditionalSelectedQChain
      (claim2NativeAFreeSelectedQStep F Target Left Right
        jLeft jRight X iLeft iRight hn) k initial terminal)
    (hk : 0 < k)
    (hGlobalAMin :
      ∀ {Z : Type} (Candidate : Structure L Z)
        (hCandidate : F Candidate) (g : Z → UT),
        Candidate.IsEHNHomomorphismEmbedding Target g →
        Nat.card {v : initial.Carrier //
          initial.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
        Nat.card {z : Z //
          g z ∈ fullFreeLeftExclusiveTarget iLeft jLeft})
    (hBMinAtA :
      ∀ {Z : Type} (Candidate : Structure L Z)
        (hCandidate : F Candidate) (g : Z → UT),
        Candidate.IsEHNHomomorphismEmbedding Target g →
        Nat.card {z : Z //
          g z ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
        Nat.card {v : initial.Carrier //
          initial.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} →
        Nat.card {v : initial.Carrier //
          initial.f v ∈ fullFreeRightExclusiveTarget iRight jRight} ≤
        Nat.card {z : Z //
          g z ∈ fullFreeRightExclusiveTarget iRight jRight}) :
    claim2NativeTotalASourceCount initial <
      claim2NativeTotalASourceCount terminal := by
  have hBBudget :=
    claim2NativeAFreeQChain_globalBBudget
      F Target Left Right jLeft jRight X iLeft iRight
      hn hChain
  have hBStrict :
      Nat.card {w : terminal.Carrier //
        terminal.f w ∈ fullFreeRightExclusiveTarget iRight jRight} <
      Nat.card {v : initial.Carrier //
        initial.f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
    change k +
      Nat.card {w : terminal.Carrier //
        terminal.f w ∈ fullFreeRightExclusiveTarget iRight jRight} ≤
      Nat.card {v : initial.Carrier //
        initial.f v ∈ fullFreeRightExclusiveTarget iRight jRight}
        at hBBudget
    omega
  have hAStrict :=
    globalLexMin_strictB_forces_strictAIncrease
      F Target initial.source initial.f
      terminal.source terminal.forbidden terminal.f terminal.hom
      (fullFreeLeftExclusiveTarget iLeft jLeft)
      (fullFreeRightExclusiveTarget iRight jRight)
      hGlobalAMin hBMinAtA hBStrict
  exact hAStrict

end AllThoseRamseyClasses.Lifts
