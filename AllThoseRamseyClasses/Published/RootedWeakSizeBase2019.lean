import AllThoseRamseyClasses.Published.RootedWeakSizeGluing2019

/-!
# The rooted weak-size K-completion invariant has a GENUINE j=0 base

The proposed strengthened invariant W_j^A(D) keeps a FULL prescribed
embedded closed A∈K outside its weak free-vertex budget j. It is not
a theorem that the ordinary W_j invariant implies W_j^A.

Nonetheless W_0^A(D) is not an invented axiom: for T=empty, the exact
induced test on T U range(a) is literally the full embedded copy of A
in D. This test has an induced 2019 corrected K-completion into A,
independent of the choice of D or its own closedness.

We also prove the natural downward monotonicity of W_j^A.
Constructing the native j->j+1 successor pass preserving this
rooted invariant remains OPEN, as does the universal common A-root
for the transverse line history.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Base W_0^A(D) holds as soon as the fixed A is an ordinary
irreducible K-member. The old control D need not itself be closed.
The exact weak tested structure is the actual induced A-copy. -/
theorem has2019_rooted_weaksize_base_zero
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {VD VA : Type v}
    [Finite VA]
    (D : RelStructure L VD)
    (A : RelStructure L VA)
    (hAK : K A) (hAIrred : A.Irreducible) :
    Has2019RootedWeakSizeCompletions K rules D A 0 := by
  classical
  intro T a hSize
  have hT : T = ∅ :=
    Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hSize)
  subst T
  have hRange (x : Set.range a) :
      ∃ y : VA, (inclusion D (Set.range a)) x = a y := x.2
  let g : Embedding (D.induce (Set.range a)) A :=
    (inclusion D (Set.range a)).factorThroughRange a hRange
  have hProtected :
      IsInducedClosedUHomomorphismEmbedding rules
        (D.induce (Set.range a)) A g :=
    IsClosedUHomomorphismEmbedding.toInducedClosed
      (g.isClosedUHomomorphismEmbedding rules)
  have hCompletion :
      HasInducedClosedUKCompletion K rules
        (D.induce (Set.range a)) :=
    ⟨VA, inferInstance, A, hAK, hAIrred, g, hProtected⟩
  simpa using hCompletion

/-- Rooted weak-size completion is monotone in the allowed number
of extra weak vertices. This does not produce an increment. -/
theorem has2019_rooted_weaksize_mono
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {VD VA : Type v}
    (D : RelStructure L VD) (A : RelStructure L VA)
    {j k : ℕ} (hkj : k ≤ j)
    (h : Has2019RootedWeakSizeCompletions K rules D A j) :
    Has2019RootedWeakSizeCompletions K rules D A k := by
  intro T a hSize
  exact h T a (hSize.trans hkj)

end AllThoseRamseyClasses.Published
