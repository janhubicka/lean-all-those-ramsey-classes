import AllThoseRamseyClasses.Published.InducedClosed2019MainContract
import PartiteConstruction.Ramsey.ClosureRelativeControlRamsey

/-!
# A constructed rank-one case of the repaired 2019 proof

The published Theorem 2.18 requires the general induction on U-size.
At rank one, an actual Ramsey witness is already constructed by the
native initial picture and finite relative-profile Picture pass in the
pinned partite-construction library. This file applies THAT constructed
case to the paper's exact induced-test local-completion axiom.

This is a positive restricted result, NOT a proof of unrestricted
Lemma 2.29 or Theorem 2.18. In particular the following assumptions
must remain visible:
* A and B are U-closed, A embeds into B, B belongs to K;
* every A-copy in C0 has U-closed RANGE relative to C0;
* the given local cutoff n(B,C0) satisfies n <= 1.
Neither arbitrary nonclosed controls nor rank j -> j+1 are supplied.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P : Type v}

/-- The native partite iteration produces an ACTUAL finite K-Ramsey
witness for a closed pair with relative A-copies and cutoff <= 1.
The local hypothesis is the paper-faithful coordinated induced test
condition, NOT the stronger abstract embedded-test definition. -/
theorem inducedClosed2019_cutoff_one_relative_copies
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (A : RelStructure L U) (B : RelStructure L V)
    (C0 : RelStructure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (hBIrr : B.Irreducible) (hKB : K B)
    (hC0 : C0.Irreducible)
    (hHer : ClosedUHereditary K rules)
    (eAB : Embedding A B)
    (hCopies : ∀ alpha : Embedding A C0,
      IsUSubstructure rules C0 (Set.range alpha))
    (n : ℕ) (hn : n ≤ 1)
    (hLocal : InducedClosedULocalCompletionAt K rules B C0 n)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : StructuralRamsey.Arrow A B C0 κ) :
    ∃ (Y : Type v) (_ : Finite Y) (Target : RelStructure L Y),
      K Target ∧ StructuralRamsey.Arrow A B Target κ := by
  exact StructuralRamsey.Partite.Induced.ramsey_of_closedLocalCompletion_cutoff_one
    A B C0 hA hB hBIrr hKB hC0 hHer eAB hCopies
    n hn hLocal.toAbstractClosed κ hArrow

end AllThoseRamseyClasses.Published
