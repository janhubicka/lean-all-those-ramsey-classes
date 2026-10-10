import AllThoseRamseyClasses.Published.Corrected4bLocalCounterexample
import AllThoseRamseyClasses.Published.LiteralWeakRankBridge
import PartiteConstruction.Ramsey.ClosureClosedLocalFiniteness

/-!
# Coordinated closed-test repair proposed for the 2019 paper

The (4b)-ONLY repair has been Lean-refuted in this repository:
\`finitePairedClass_corrected_local_cutoff\` verifies that the
non-Ramsey paired-equivalence class passes it for |C0|+1.

The intended locally finite completion axiom must therefore change
BOTH the Definition 2.15 MAP notion and Definition 2.17(4b):

* U-irreducibility itself stays intrinsically defined as printed;
* a U-homomorphism-embedding protects U-closed U-irreducible
  substructures, not ALL nonclosed intrinsic weak tests;
* corrected (4b) asks membership of those same CLOSED tests;
* (4a) retains its completion wording but uses the amended map;
* (4c) retains ALL exact weak n-vertex induced tests, using the
  amended map for each of their (K,U)-completions;
* n(B,C0) and the B-copywise conclusion are unchanged.

The definitions \`IsClosedUHomomorphismEmbedding\`,
\`ClosedULocalCompletionAt\`, and
\`ClosedUMultiamalgamationClass\` in pinned
partite-construction express this coordinated convention,
using abstract embedded test objects rather than only their chosen
induced images.

The general corrected Ramsey theorem is a TARGET PROPOSITION, not a
proved theorem or admitted axiom. The long-cycle nonlocal-finiteness
witness for the paired class is mathematically described in
docs/paired-equivalence-local-finiteness-correction.md on the
upstream audit branch, but is not yet end-to-end Lean verified.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {V W : Type v}

/-- Explicit source-level name for the proposed map convention.
This is NOT \`IsUHomomorphismEmbedding\` of literal Definition 2.15. -/
abbrev Proposed2019UHomomorphismEmbedding
    (rules : ClosureDescription L)
    (A : RelStructure L V) (B : RelStructure L W)
    (f : V → W) : Prop :=
  IsClosedUHomomorphismEmbedding rules A B f

/-- Explicit name for the proposed coordinated local implication.
Its (4c) still quantifies over every exact weak induced test. -/
abbrev Proposed2019LocalCompletionAt
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (B : RelStructure L V) (C0 : RelStructure L W)
    (n : ℕ) : Prop :=
  ClosedULocalCompletionAt K rules B C0 n

/-- Full class of the proposed corrected first main theorem.
The word proposed is intentional: no proof is asserted. -/
abbrev Proposed2019MultiamalgamationClass
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L) : Prop :=
  ClosedUMultiamalgamationClass R K rules

/-- The corrected Theorem 2.18 is the following OPEN proof target,
not a new axiom. Unlike CorrectedTheorem218Target, this changes the
Definition 2.15 map convention as well as clause (4b). -/
def Proposed2019Theorem218Target : Prop :=
  ∀ (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L),
    FiniteRamseyClass R →
    (∀ {X : Type v} (C : RelStructure L X),
      R C → C.Irreducible) →
    Proposed2019MultiamalgamationClass R K rules →
    FiniteRamseyClass K

/-- The stronger interim all-intrinsic-test proof invariant in
LiteralWeakRankBridge really implies the intended CLOSED-test map,
but the reverse implication is not asserted (and is generally false
for weak nonclosed tests). -/
theorem fullyProtected_implies_proposedMap
    {rules : ClosureDescription L}
    {A : RelStructure L V} {B : RelStructure L W}
    {f : V → W}
    (h : IsFullyProtectedUHomomorphismEmbedding rules A B f) :
    Proposed2019UHomomorphismEmbedding rules A B f := by
  refine ⟨h.1, ?_⟩
  intro X Test _ hIrred e
  exact h.2 Test hIrred e

end AllThoseRamseyClasses.Published
