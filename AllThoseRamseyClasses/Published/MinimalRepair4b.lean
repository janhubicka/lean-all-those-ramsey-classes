import AllThoseRamseyClasses.Published.LiteralLocalFiniteness
import PartiteConstruction.Ramsey.ClosureClosedLocalFiniteness

/-!
# Minimal proposed correction of 2019 Definition 2.17(4b)

The only semantic change is that the structures tested for membership
in K in clause (4b) must also be U-CLOSED.

Everything else stays exactly as published:
* U-irreducible uses the intrinsic 2019 definition;
* (4a) uses the original 2019 U-completion maps protecting EVERY
  intrinsic U-irreducible test, including nonclosed weak tests;
* (4c) asks for original 2019 K,U-completions of EVERY induced
  weak substructure on at most n vertices;
* no additional closedness of C0 is assumed;
* conclusion: one K-valued B-copywise completion.

In particular the different, weaker experimental
IsClosedUHomomorphismEmbedding from partite-construction is NOT
used by this corrected theorem contract.

Theorem 2.18 for this corrected axiom is NOT claimed proved.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {V W P : Type v}

/-- Preferred literal 2019 Definition 2.17(4b) repair:
only U-CLOSED intrinsically U-irreducible induced tests must
belong to K. The intrinsic irreducibility predicate is unchanged. -/
def CorrectedUIrreduciblesIn
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (C : RelStructure L V) : Prop :=
  ∀ S : Set V,
    IsUClosed rules (C.induce S) →
    IsUIrreducible rules (C.induce S) →
    K (C.induce S)

/-- The preferred minimal corrected Definition 2.17(4).
Only (4b) differs from LiteralULocalCompletionAt.
The completion map (4a) and all weak n-vertex tests (4c)
remain the exact PUBLISHED ones. -/
def CorrectedULocalCompletionAt
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (B : RelStructure L W)
    (C0 : RelStructure L P)
    (n : ℕ) : Prop :=
  ∀ {X : Type v} [Finite X] (C : RelStructure L X),
    IsUClosed rules C →
    IsUCompletion rules C C0 →
    CorrectedUIrreduciblesIn K rules C →
    (∀ S : Finset X, S.card ≤ n →
      HasLiteralUKCompletion K rules (C.induce (↑S : Set X))) →
    HasCopywiseCompletion K B C

/-- The corrected local axiom is genuinely STRONGER than the
printed one: every printed (4b) test in K implies the corrected
(4b) membership antecedent. This proves only the easy direction,
not equivalence of the hypotheses. -/
theorem CorrectedULocalCompletionAt.toLiteral
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {B : RelStructure L W} {C0 : RelStructure L P}
    {n : ℕ}
    (h : CorrectedULocalCompletionAt K rules B C0 n) :
    LiteralULocalCompletionAt K rules B C0 n := by
  intro X hX C hClosed hProj hAll hSmall
  apply h C hClosed hProj
  · intro S _ hIrred
    exact hAll S hIrred
  · exact hSmall

/-- Testing more small weak substructures can only strengthen the
antecedent, and thus preserves the corrected local implication. -/
theorem CorrectedULocalCompletionAt.mono
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {B : RelStructure L W} {C0 : RelStructure L P}
    {n m : ℕ}
    (h : CorrectedULocalCompletionAt K rules B C0 n)
    (hnm : n ≤ m) :
    CorrectedULocalCompletionAt K rules B C0 m := by
  intro X hX C hClosed hProj hCover hSmall
  exact h C hClosed hProj hCover
    (fun S hS => hSmall S (hS.trans hnm))

/-- Corrected (4b) is automatically satisfied by every K-member
under precisely the CLOSED hereditary property of the paper.
Unlike printed (4b), it is not excluded by absence of singleton
members of K. No ordinary hereditary assumption is used. -/
theorem CorrectedUIrreduciblesIn.of_mem
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (hHer : ClosedUHereditary K rules)
    (C : RelStructure L V) (hC : K C) :
    CorrectedUIrreduciblesIn K rules C := by
  intro S hClosed _
  exact hHer (C.induce S) C hC hClosed (inclusion C S)

end AllThoseRamseyClasses.Published
