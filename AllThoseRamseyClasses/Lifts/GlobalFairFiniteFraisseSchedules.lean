import AllThoseRamseyClasses.Lifts.GlobalCountableFraisseExtensionDiagrams
import Mathlib.Logic.Encodable.Basic

/-!
# Track F — fair schedules from countability of actual finite age diagrams

The original global maximal-trace age has a countable set of
actual labelled representatives, and the genuine finite FULL
extension diagrams between them form another countable type.

For ANY countable type α, define an explicit finite prefix list
at stage n by decoding every index k < n+1. Every α-element
then belongs to ALL sufficiently late prefix lists, using the
usual Encodable.decode_encode law. Thus the schedule is FAIR:
an extension diagram is not considered only once before its
root appears; it is scheduled again at every sufficiently
late stage.

Apply this to actual finite maximal-trace representatives and
full extension diagrams. The output is a pair of NAT-indexed
FINITE lists, ready for the verified one-stage schedulers.

This does NOT construct a countable direct limit or its
ultrahomogeneity; it supplies only exact finite fair
bookkeeping. It has no hidden uniform bound on source sizes
or relation/function arities, and no weak EHN map occurs.
The numbered ramsey.tex is frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
universe u v
variable {L : Language.{u}}

/-- At stage n, list every α-element whose chosen countable code
is among the first n+1 naturals. Each list is genuinely finite.
The decoder only serves as finite bookkeeping, not as a new
mathematical axiom about the finite-age class. -/
noncomputable def countablePrefixList
    (α : Type v) [Countable α] (n : ℕ) : List α := by
  classical
  letI : Encodable α := Encodable.ofCountable α
  exact (List.range (n + 1)).filterMap (Encodable.decode (α := α))

/-- Every element of a countable type is listed at EVERY stage
after its code, not just at one particular stage. This is the
fairness property needed for Fraisse extension diagrams to be
handled after new root copies first appear. -/
theorem countablePrefixList_eventually_mem
    (α : Type v) [Countable α] (a : α) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      a ∈ countablePrefixList α n := by
  classical
  letI : Encodable α := Encodable.ofCountable α
  refine ⟨Encodable.encode a, ?_⟩
  intro n hn
  change a ∈ (List.range (n + 1)).filterMap (Encodable.decode (α := α))
  apply (List.mem_filterMap).2
  refine ⟨Encodable.encode a, ?_, ?_⟩
  · exact List.mem_range.mpr (Nat.lt_succ_of_le hn)
  · exact Encodable.decode_encode a

/-- At each finite stage list finitely many ACTUAL original
maximal-trace age representatives, encoded from the countable
full-isomorphism cover. -/
noncomputable def globalOriginalRepresentativePrefix
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (n : ℕ) : List (GlobalOriginalFiniteTraceRepresentatives F) := by
  letI : Countable (GlobalOriginalFiniteTraceRepresentatives F) :=
    hInput.countableRepresentatives
  exact countablePrefixList (GlobalOriginalFiniteTraceRepresentatives F) n

/-- Every actual representative occurs in ALL sufficiently
late stage lists, so cofinality requests are never forgotten. -/
theorem globalOriginalRepresentativePrefix_eventually_mem
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (P : GlobalOriginalFiniteTraceRepresentatives F) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      P ∈ globalOriginalRepresentativePrefix F hInput n := by
  letI : Countable (GlobalOriginalFiniteTraceRepresentatives F) :=
    hInput.countableRepresentatives
  exact countablePrefixList_eventually_mem
    (GlobalOriginalFiniteTraceRepresentatives F) P

/-- Finite fair stage lists of genuine FULL extension diagrams
between labelled representatives of the original finite age. -/
noncomputable def globalOriginalExtensionDiagramPrefix
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (n : ℕ) : List (GlobalOriginalFiniteTraceDiagram F) := by
  letI : Countable (GlobalOriginalFiniteTraceDiagram F) :=
    globalOriginalFiniteTraceDiagrams_countable F hInput
  exact countablePrefixList (GlobalOriginalFiniteTraceDiagram F) n

/-- Every given full extension diagram is scheduled at EVERY
sufficiently late stage. This is stronger than occurrence once:
it ensures that copies first appearing at a late stage can
still be extended at some later stage. -/
theorem globalOriginalExtensionDiagramPrefix_eventually_mem
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (d : GlobalOriginalFiniteTraceDiagram F) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      d ∈ globalOriginalExtensionDiagramPrefix F hInput n := by
  letI : Countable (GlobalOriginalFiniteTraceDiagram F) :=
    globalOriginalFiniteTraceDiagrams_countable F hInput
  exact countablePrefixList_eventually_mem
    (GlobalOriginalFiniteTraceDiagram F) d

end AllThoseRamseyClasses.Lifts
