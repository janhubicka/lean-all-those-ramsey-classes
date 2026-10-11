import AllThoseRamseyClasses.Published.CoordinatedWeakGadgetEAgreement
import AllThoseRamseyClasses.Published.CoordinatedWeakRelatedCompletion
import AllThoseRamseyClasses.Published.CoordinatedWeakOrderReflection

/-!
# Exact weak n-vertex local completions for every long-cycle Cn

For ANY cutoff k, let Ck be the concrete U-closed relational
matching cycle, and S ANY subset of its vertices with |S|<=k
(including arbitrary nonclosed weak subsets missing mates).

The finite K structure D(k,S) was constructed in PR #81.
Its matching M is unchanged, and its total order agrees with Ck on
every gadget-related pair (PR #83). The uniform path/closing
E-gadget proof establishes complete E reflection on all such
pairs for exact S (PR #91).

This module combines those facts: the canonical weak inclusion
Ck|S -> D(k,S) is positive and restricts to an induced embedding
on EVERY U-closed intrinsically U-irreducible source test. This
establishes the full proposed coordinated (4c), at *each* cutoff
k, with no change to the tested vertices or use of a closure hull.

All mathematical source claims depend explicitly on already
formalized imported theorems. A CI-green proof and axioms audit
is required before certifying the claimed all-k (4c) statement.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The three relations all agree with the actual Ck source on
every gadget-related ordered pair belonging to the original
weak tested S of size <= k. No U-closedness assumption on S. -/
theorem cycleWeak_relatedAgreement
    (k : ℕ) (S : Finset (CycleVertex k))
    (hCard : S.card ≤ k) :
    CycleWeakRelatedAgreement k S := by
  intro R x y hx hy hRelated
  cases R with
  | lt =>
      exact cycleWeakCandidate_lt_iff_of_related
        k S x y hRelated
  | equiv =>
      exact cycleWeakCandidate_E_iff_of_related
        k S hCard x y hx hy hRelated
  | mate =>
      exact cycleWeakCandidate_mate_iff k S x y

/-- The full coordinated Definition 2.17(4c) holds for this
explicit Ck, for all exact WEAK n-vertex tests, not only
closed substructures or their U-closures. -/
theorem cycleGadgetWitness_all_weak_K_completions (k : ℕ) :
    ∀ S : Finset (CycleVertex k), S.card ≤ k →
      HasClosedUKCompletion finitePairedClass mateRules
        ((cycleGadgetWitness k).induce
          (↑S : Set (CycleVertex k))) := by
  intro S hCard
  exact cycleWeak_hasClosedUKCompletion_of_related
    k S (cycleWeak_relatedAgreement k S hCard)

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
