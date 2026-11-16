import AllThoseRamseyClasses.Lifts.Claim2AFreeSelectedQChainMonotonicity
import Mathlib.Tactic

/-!
# Track B: exact total PRIVATE Q-nonroot A-source cost of a finite chain

The older A-free selected-Q chain proves A_total never decreases and
B_total strictly decreases, but it does not provide a proof object
recording how many newly inserted A-exclusive SOURCE vertices each
genuine selected-Q amalgam contributes.

Here each edge stores its SAME chosen native Q, old complete E
complement, full Q+E free-amalgam, old inner A-freeness, exact
old/new E-coordinate agreement, strict B-SOURCE descent and the
LITERAL private-Q A-source cardinality. Thus the count cannot
refer to an independently invented replacement Q.

The costed chain stores a natural number for the sum of these
private-Q costs, and proves EXACT telescope:
    totalA(terminal) = totalA(initial) + totalPrivateQCost.
At the same time:
    length + totalB(terminal) <= totalB(initial).

The proof intentionally does not assume original A-minimality at
intermediate states, that the Q cost vanishes, or that capture,
A-mixedness and initial weak-map collisions are absent.
No new axiom, weak-image quotient or edits to frozen 2019 TeX.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- SAME actual A-free native Q+E replacement as the previous step
relation, with the exact cardinality of its own Q-private source
vertices mapped into A-exclusive TARGET region stored on the edge. -/
def claim2NativeAFreeQStepWithPrivateCost
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
    (privateACost : ℕ) : Prop :=
    claim2NativeGeometricStep F Target Left Right
      jLeft jRight X iLeft iRight hn s t ∧
    ∃ (m : ℕ) (inner : GeometricFunctionalPieceData s.source m),
      0 < m ∧
      geometricPieceVertices s.source inner ⊆
        geometricPieceVertices s.source s.outer ∧
      (∀ z : s.Carrier,
        z ∈ functionalComponentFrom s.source
          (Set.range inner.roots) inner.left →
        z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) s.f) ∧
      ∃ (Q : FunctionalRootExtension
          (geometricGlobalFunctionalChart s.source inner).root),
        (FunctionalRootExtension.toEnumeratedRootedPattern
            (geometricGlobalFunctionalChart s.source inner).root
            (Equiv.refl (Fin m)) Q) ∈
          forbiddenGeometricFunctionalPieces F m ∧
        ∃ (iQ : Structure.Embedding Q.str t.source)
          (iE : Structure.Embedding
            (geometricGlobalComplementChart s.source inner).str t.source),
          Structure.IsFreeAmalgam
            Q.rootEmbedding
            (geometricGlobalComplementChart s.source inner).rootEmbedding
            iQ iE ∧
          (∀ q : Q.Carrier,
            t.f (iQ q) ∉ fullFreeRightExclusiveTarget iRight jRight) ∧
          (∀ e : (geometricGlobalComplementChart s.source inner).Carrier,
            t.f (iE e) = s.f e.1) ∧
          (iQ '' (Set.univ : Set Q.Carrier) ∪
             iE '' (oldOuterContextInInnerComplement s.source
               s.outer inner)) =
            geometricPieceVertices t.source t.outer ∧
          Nat.card {q : Q.Carrier //
            q ∉ Set.range Q.rootEmbedding ∧
            t.f (iQ q) ∈ fullFreeLeftExclusiveTarget iLeft jLeft} = privateACost



/-- Forget only the numerical Q-private A-cost on a SAME native
selected-Q source edge. The actual Q+E diagram remains unchanged. -/
theorem claim2NativeAFreeQStepWithPrivateCost.toAFreeStep
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
    (cost : ℕ)
    (hStep : claim2NativeAFreeQStepWithPrivateCost F Target Left Right
      jLeft jRight X iLeft iRight hn s t cost) :
    claim2NativeAFreeSelectedQStep F Target Left Right
      jLeft jRight X iLeft iRight hn s t := by
  rcases hStep with ⟨hNative, m, inner, hm, hInside, hNoA,
    Q, hSelected, iQ, iE, hFree, hNoB, hEAgree,
    hOuter, _hCost⟩
  exact ⟨hNative, m, inner, hm, hInside, hNoA, Q,
    hSelected, iQ, iE, hFree, hNoB, hEAgree, hOuter⟩

/-- Every actual A-free selected-Q edge has a canonical numerical
private A-SOURCE cost, witnessed by the *same Q* in its proof term. -/
theorem claim2NativeAFreeQStep_existsPrivateCost
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
    (hStep : claim2NativeAFreeSelectedQStep F Target Left Right
      jLeft jRight X iLeft iRight hn s t) :
    ∃ cost : ℕ,
      claim2NativeAFreeQStepWithPrivateCost F Target Left Right
        jLeft jRight X iLeft iRight hn s t cost := by
  rcases hStep with ⟨hNative, m, inner, hm, hInside, hNoA,
    Q, hSelected, iQ, iE, hFree, hNoB, hEAgree, hOuter⟩
  exact ⟨Nat.card {q : Q.Carrier //
       q ∉ Set.range Q.rootEmbedding ∧
       t.f (iQ q) ∈ fullFreeLeftExclusiveTarget iLeft jLeft},
    hNative, m, inner, hm, hInside, hNoA, Q,
    hSelected, iQ, iE, hFree, hNoB, hEAgree,
    hOuter, rfl⟩

/-- The SOURCE A-support difference of a cost-annotated step is
EXACTLY the numerical cost of the chosen private Q-nonroots.
This is an identity, not merely monotonicity or a bound on images. -/
theorem claim2NativeAFreeQStepWithPrivateCost_exactTotalA
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
    (cost : ℕ)
    (hStep : claim2NativeAFreeQStepWithPrivateCost F Target Left Right
      jLeft jRight X iLeft iRight hn s t cost) :
    claim2NativeTotalASourceCount t =
      claim2NativeTotalASourceCount s + cost := by
  rcases hStep with ⟨_hNative, m, inner, _hm, _hInside,
      hNoA, Q, _hSelected, iQ, iE, hFree, _hNoB,
      hEAgree, _hOuter, hCost⟩
  have hOldNoA :
      ∀ z : s.Carrier,
        z ∈ functionalComponentFrom s.source
          (Set.range inner.roots) inner.left →
        s.f z ∉ fullFreeLeftExclusiveTarget iLeft jLeft := by
    intro z hz hzA
    exact hNoA z hz
      ((weakFreeLeftPart_iff_targetExclusive
        iLeft jLeft s.f z).mpr hzA)
  have hExact :=
    geometricSelectedQ_AfreeOld_exact_Aactive_cost
      s.source inner Q t.source t.finite iQ iE hFree
      s.f t.f (fullFreeLeftExclusiveTarget iLeft jLeft)
      hOldNoA hEAgree
  change
    Nat.card {w : t.Carrier //
      t.f w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
    Nat.card {v : s.Carrier //
      s.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} + cost
  simpa only [hCost] using hExact

/-- A chain of LITERAL A-free selected-Q full-native steps, with
the exact Q-private A-source costs added in order. Unlike merely
listing costs, its proof term keeps the actual chosen Q of EACH
step and full original source embedding data. -/
inductive Claim2NativeAFreeQCostedChain
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    {n : ℕ} (hn : 0 < n) :
    ℕ →
    Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n →
    Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n →
    ℕ → Prop where
  | nil (s : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n) :
      Claim2NativeAFreeQCostedChain F Target Left Right
        jLeft jRight X iLeft iRight hn 0 s s 0
  | cons {k : ℕ}
      {s t u : Claim2NativeGeometricState F Target Left Right
        jLeft jRight X iLeft iRight n}
      {cost tailCost : ℕ}
      (hStep : claim2NativeAFreeQStepWithPrivateCost
        F Target Left Right jLeft jRight X iLeft iRight
        hn s t cost)
      (hTail : Claim2NativeAFreeQCostedChain F Target Left Right
        jLeft jRight X iLeft iRight hn k t u tailCost) :
      Claim2NativeAFreeQCostedChain F Target Left Right
        jLeft jRight X iLeft iRight hn
        (k + 1) s u (cost + tailCost)

/-- Project the detailed private-Q costed chain back to the
usual A-free native Q+E full source-step chain, without any
loss of its initial/terminal source state or length. -/
theorem claim2NativeAFreeQCostedChain_toAFreeChain
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
    {k cost : ℕ}
    {s t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n}
    (hChain : Claim2NativeAFreeQCostedChain F Target Left Right
      jLeft jRight X iLeft iRight hn k s t cost) :
    ConditionalSelectedQChain
      (claim2NativeAFreeSelectedQStep F Target Left Right
        jLeft jRight X iLeft iRight hn) k s t := by
  induction hChain with
  | nil s =>
      exact ConditionalSelectedQChain.nil s
  | cons hStep hTail ih =>
      exact ConditionalSelectedQChain.cons
        (claim2NativeAFreeQStepWithPrivateCost.toAFreeStep
          F Target Left Right jLeft jRight X iLeft iRight
          hn _ _ _ hStep) ih

/-- Every finite full-native A-free selected-Q source chain can
be refined into a chain recording each SAME selected Q's exact
private A-source cardinality. This adds no new source step. -/
theorem claim2NativeAFreeQChain_existsCosted
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
      (claim2NativeAFreeSelectedQStep F Target Left Right
        jLeft jRight X iLeft iRight hn) k s t) :
    ∃ cost : ℕ,
      Claim2NativeAFreeQCostedChain F Target Left Right
        jLeft jRight X iLeft iRight hn k s t cost := by
  induction hChain with
  | nil s =>
      exact ⟨0, Claim2NativeAFreeQCostedChain.nil s⟩
  | cons hStep hTail ih =>
      obtain ⟨cost, hCostStep⟩ :=
        claim2NativeAFreeQStep_existsPrivateCost
          F Target Left Right jLeft jRight X iLeft iRight
          hn _ _ hStep
      obtain ⟨tailCost, hCostTail⟩ := ih
      exact ⟨cost + tailCost,
        Claim2NativeAFreeQCostedChain.cons hCostStep hCostTail⟩

/-- Exact SOURCE-cardinality telescoping over the actual chosen
selected Q in EVERY edge:
totalA(terminal) = totalA(initial) + totalPrivateQCost. -/
theorem claim2NativeAFreeQCostedChain_exactTotalA
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
    {k cost : ℕ}
    {s t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n}
    (hChain : Claim2NativeAFreeQCostedChain F Target Left Right
      jLeft jRight X iLeft iRight hn k s t cost) :
    claim2NativeTotalASourceCount t =
      claim2NativeTotalASourceCount s + cost := by
  induction hChain with
  | nil s =>
      rfl
  | cons hStep hTail ih =>
      have hOne :=
        claim2NativeAFreeQStepWithPrivateCost_exactTotalA
          F Target Left Right jLeft jRight X iLeft iRight
          hn _ _ _ hStep
      omega

/-- Strict GLOBAL B-SOURCE decrease independently of the exact
Q-private A cost; the selected Q and full native source diagram
remain attached to EVERY costed edge. -/
theorem claim2NativeAFreeQCostedChain_globalBBudget
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
    {k cost : ℕ}
    {s t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n}
    (hChain : Claim2NativeAFreeQCostedChain F Target Left Right
      jLeft jRight X iLeft iRight hn k s t cost) :
    k + claim2NativeTotalBSourceCount t ≤
      claim2NativeTotalBSourceCount s := by
  exact claim2NativeAFreeQChain_globalBBudget
    F Target Left Right jLeft jRight X iLeft iRight hn
    (claim2NativeAFreeQCostedChain_toAFreeChain
      F Target Left Right jLeft jRight X iLeft iRight hn hChain)

end AllThoseRamseyClasses.Lifts
