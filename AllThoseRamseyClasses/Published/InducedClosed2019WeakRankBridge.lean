import AllThoseRamseyClasses.Published.InducedClosedLogicalDirection
import PartiteConstruction.Ramsey.ClosureClosedCompletionRank

/-!
# 2019 Lemma 2.31: exact weak tests from the closed U-size invariant

This is the missing *logical handoff*, not the higher-rank constructor
claimed in the published proof of Lemma 2.30.

Definition 2.17(4c), UNCHANGED under the proposed coordinated repair,
tests every vertex-exact weak induced substructure of C with at most
n vertices. The source of such a test need not be U-closed.

One may use its closure in C as an INTERMEDIATE object to apply a
rank-n construction invariant, but the resulting K-completion is
restricted back to the ORIGINAL weak vertex set. No test is silently
replaced by its generated closure.

The stronger embedded-closed-map invariant on closed hulls is a
sufficient *proof invariant*. It is not a redefinition of the paper's
completion map, which quantifies over induced tests. The last step
converts to that paper-faithful convention.

The entire rank-n assumption is explicit. The unproved j -> j+1
Picture step producing such a witness is NOT smuggled into a theorem.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- The exact statement that closed generating rank <= n has a
K-completion by the stronger abstract closed-test map. This is a
construction invariant, not a premise of Definition 2.17(4c). -/
def Has2019ClosedRankCompletions
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (C : RelStructure L V) (n : ℕ) : Prop :=
  ∀ (T : Set V) [Fintype T],
    IsUClosed rules (C.induce T) →
    USize rules (C.induce T) ≤ n →
    HasClosedUKCompletion K rules (C.induce T)

/-- Corrected 2019 Lemma 2.31, precisely the final passage from
rank-bounded U-CLOSED hulls to ALL weak induced tests in (4c).

The bound is S.card, the original number of vertices, not the size
of its closure. The finite K-target and the map are reused on S. -/
theorem lemma_2_31_exact_weak_tests_of_closed_rank
    [Finite V]
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (C : RelStructure L V)
    (hC : IsUClosed rules C) (n : ℕ)
    (hRank : Has2019ClosedRankCompletions K rules C n) :
    ∀ S : Finset V, S.card ≤ n →
      HasInducedClosedUKCompletion K rules
        (C.induce (↑S : Set V)) := by
  intro S hS
  have hAbstract :
      HasClosedUKCompletion K rules
        (C.induce (↑S : Set V)) :=
    HasClosedUKCompletion.of_closed_USize
      rules C hC n hRank S hS
  exact HasClosedUKCompletion.toInducedClosed hAbstract

/-- The output of a rank-controlled picture indeed discharges the
ORIGINAL 2019 induced-test (4c), including the empty test and
nonclosed tests. The colour/Ramsey and control-map invariants of
the Picture must be supplied separately by its actual construction. -/
theorem lemma_2_31_local_clause_c_of_closed_rank
    [Finite V]
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {C : RelStructure L V} {n : ℕ}
    (hC : IsUClosed rules C)
    (hRank : Has2019ClosedRankCompletions K rules C n)
    (S : Finset V) (hS : S.card ≤ n) :
    HasInducedClosedUKCompletion K rules
      (C.induce (↑S : Set V)) :=
  lemma_2_31_exact_weak_tests_of_closed_rank
    K rules C hC n hRank S hS

end AllThoseRamseyClasses.Published
