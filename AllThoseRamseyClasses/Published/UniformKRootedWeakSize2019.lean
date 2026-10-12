import AllThoseRamseyClasses.Published.RootedWeakProjectionPreservation2019

/-!
# A uniform rooted weak-size invariant with ALL closed irreducible K-roots

The rooted weak invariant W_j^A introduced in PR #150 works with ONE
fixed A, and the conditional A-covered Picture hypothesis in PR #159
need not hold in general (e.g. incompatible unary types).

The natural replacement is a UNIFORM rooted invariant:

  U_j(D): for EVERY finite intrinsically U-closed U-irreducible
  K-member Q, every full embedding a:Q->D, and every weak vertex
  set T of cardinality <=j, the EXACT induced old test on
  T U a[Q] has a corrected K-completion.

The whole root Q is NOT charged to the j free weak vertices,
so arbitrarily large singleton-generated closure roots remain allowed.

This file proves that U_0(D) is genuinely constructible for ANY D
when K-members are ordinarily irreducible: with T empty, the exact
tested structure is an embedded Q and completes into Q itself.

It also proves U_j(D) is downward monotone, and — CRUCIALLY —
U_j(C) is preserved by ANY corrected protected projection C->D
when U_j(D) holds. The preservation applies the previously verified
rooted W_j^Q theorem for each fixed closed U-irreducible Q.

This is a strong but completely explicit recursive invariant.
It is NOT proved to follow from the ordinary unrooted W_j(D),
and its genuine native j->j+1 Hales--Jewett construction is still
OPEN. No corrected full Ramsey Theorem 2.18 is claimed.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Completion of every exact weak j-vertex subset together with
ANY prescribed full embedded closed U-irreducible K-root.
The root is not included in the j extra-vertex budget. -/
def Has2019UniformKRootedWeakSize
    {VD : Type v}
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (D : RelStructure L VD) (j : ℕ) : Prop :=
  ∀ {VQ : Type v} [Finite VQ] (Q : RelStructure L VQ),
    K Q → IsUClosed rules Q → IsUIrreducible rules Q →
    (T : Finset VD) (a : Embedding Q D), T.card ≤ j →
      HasInducedClosedUKCompletion K rules
        (D.induce ((↑T : Set VD) ∪ Set.range a))

/-- Uniform rooted rank ZERO requires no Picture construction:
for T empty, the original weak test is exactly a full induced Q-copy;
its completion target Q∈K is ordinarily irreducible by the class
hypothesis. No closure of the weak test is substituted. -/
theorem has2019_uniform_K_rooted_base_zero
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {VD : Type v}
    (D : RelStructure L VD)
    (hKIrr : ∀ {Z : Type v} (T : RelStructure L Z),
      K T → T.Irreducible) :
    Has2019UniformKRootedWeakSize K rules D 0 := by
  intro VQ hVQ Q hKQ _ _ T a hT
  have hBase : Has2019RootedWeakSizeCompletions K rules D Q 0 :=
    has2019_rooted_weaksize_base_zero D Q hKQ (hKIrr Q hKQ)
  exact hBase T a hT

/-- Uniform rooted weak-size completion is downward monotone. -/
theorem has2019_uniform_K_rooted_mono
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {VD : Type v}
    (D : RelStructure L VD)
    {j k : ℕ} (hkj : k ≤ j)
    (hOld : Has2019UniformKRootedWeakSize K rules D j) :
    Has2019UniformKRootedWeakSize K rules D k := by
  intro VQ hVQ Q hQK hQClosed hQUIrred T a hT
  exact hOld Q hQK hQClosed hQUIrred T a (hT.trans hkj)

/-- Uniform rooted weak-size completions pull back along ANY corrected
protected Picture projection. The quantification over arbitrary
closed U-irreducible K-roots is preserved exactly: each prescribed
Q-copy survives as a full embedding in the old Picture, by protection.

No extra fixed-A-cover hypothesis, projection injectivity or global
U-closedness of C is used. This is preservation at SAME j, not a
construction of U_(j+1) from U_j. -/
theorem has2019_uniform_K_rooted_of_protected_projection
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {VC VD : Type v}
    (C : RelStructure L VC)
    (D : RelStructure L VD)
    (p : VC → VD)
    (hp : IsInducedClosedUHomomorphismEmbedding rules C D p)
    (j : ℕ)
    (hOld : Has2019UniformKRootedWeakSize K rules D j) :
    Has2019UniformKRootedWeakSize K rules C j := by
  intro VQ hVQ Q hQK hQClosed hQUIrred T a hT
  have hRooted : Has2019RootedWeakSizeCompletions K rules D Q j := by
    intro S b hCard
    exact hOld Q hQK hQClosed hQUIrred S b hCard
  have hPreserved : Has2019RootedWeakSizeCompletions
      K rules C Q j :=
    has2019_rooted_weaksize_of_protected_projection
      C D Q hQClosed hQUIrred p hp j hRooted
  exact hPreserved T a hT

end AllThoseRamseyClasses.Published
