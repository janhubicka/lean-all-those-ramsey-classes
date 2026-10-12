import AllThoseRamseyClasses.Published.RootedWeakOneAnchor2019

/-!
# Complete weak j+1 tests using a VARIABLE closed K-anchor in Old

The one-vertex rooted completion theorem (merged PR #156) used a
FIXED root A. A stronger uniform rooted invariant can avoid the
false global A-covered hypothesis: every old vertex need only lie
in SOME finite closed U-irreducible Q∈K embedded in Old. The root
Q may vary with the chosen vertex and may have arbitrarily many
closure-generated vertices.

This file proves the direct conditional bridge, independently of
HOW this varying K-anchor coverage and uniform rooted invariant
are constructed:

Suppose the old D carries
  (1) a full embedded closed U-irreducible K-root through EVERY
      vertex, and
  (2) rooted exact weak j-vertex K-completions for EVERY such root.
Then ANY NONEMPTY finite exact weak source of <=j+1 vertices with
a corrected protected map into D is already K-completable.

Choose ANY original source vertex x; anchor its old image f(x)
inside a closed K-root Q_x; the remaining at most j vertices are
the weak additional support T. Completing the induced old test
T U Q_x by the uniform rooted premise and pulling the completion
back finishes the original exact source.

The chosen Q_x is NOT required equal to the selected Ramsey A,
and no bound |Q_x|<=j is postulated. No source intrinsic U-rank,
source closedness, or injectivity is assumed.

The missing substantial step is a genuine native Picture successor
maintaining this stronger uniform rooted invariant. This lemma
alone neither constructs that step nor proves corrected Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- An explicit uniform rooted j-invariant plus genuine varying
closed K-anchor coverage COMPLETES any nonempty exact weak source
of at most j+1 vertices with a corrected protected old map.

The root is allowed to contain many more than j vertices; only
the additional old weak image support is charged to the cutoff. -/
theorem inducedClosed2019_weaksize_completion_of_variable_K_anchor
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {U VD : Type v}
    [Fintype U] [Nonempty U] [Finite VD]
    (Source : RelStructure L U)
    (D : RelStructure L VD)
    (p : U → VD)
    (hp : IsInducedClosedUHomomorphismEmbedding rules Source D p)
    (j : ℕ)
    (hCard : Fintype.card U ≤ j+1)
    (hAnchor : ∀ y : VD,
      ∃ S : Set VD, y ∈ S ∧
        IsUClosed rules (D.induce S) ∧
        IsUIrreducible rules (D.induce S) ∧
        K (D.induce S))
    (hUniform :
      ∀ {VQ : Type v} [Finite VQ] (Q : RelStructure L VQ),
        K Q → IsUClosed rules Q → IsUIrreducible rules Q →
        ∀ (T : Finset VD) (a : Embedding Q D), T.card ≤ j →
          HasInducedClosedUKCompletion K rules
            (D.induce ((↑T : Set VD) ∪ Set.range a))) :
    HasInducedClosedUKCompletion K rules Source := by
  classical
  let x : U := Classical.choice ‹Nonempty U›
  obtain ⟨S, hMember, hClosed, hIrred, hK⟩ := hAnchor (p x)
  letI : Finite S :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let Q : RelStructure L S := D.induce S
  have hRootedQ :
      Has2019RootedWeakSizeCompletions K rules D Q j := by
    intro T a hT
    exact hUniform Q hK hClosed hIrred T a hT
  let a : Embedding Q D := inclusion D S
  have hHit : p x ∈ Set.range a :=
    ⟨⟨p x, hMember⟩, rfl⟩
  exact inducedClosed2019_weaksize_completion_of_one_A_anchor
    Source D Q p hp j hCard a x hHit hRootedQ

end AllThoseRamseyClasses.Published
