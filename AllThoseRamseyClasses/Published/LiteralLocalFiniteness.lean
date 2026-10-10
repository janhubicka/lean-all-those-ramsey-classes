import AllThoseRamseyClasses.Published.SingletonObstruction

/-!
# Literal Definition 2.17(4) (2019), with its exact weak tests

This is a faithful *literal* relational contract, separate from
\`ClosedULocalCompletionAt\` in partite-construction. No reinterpretation
of the published 2019 words is silently applied:

* (4a): \`C0\` is a U-completion of the *entire* U-closed candidate C,
  using the literal 2019 U-homomorphism-embedding.
* (4b): **all intrinsic U-irreducible induced substructures** of C
  belong to K, even when those tests are not U-closed.
* (4c): **all** induced weak substructures on at most n vertices must
  have a K-valued U-completion, without adjoining closure vertices
  before measuring their cardinality.
* Conclusion: a single map into K preserving each B-copy, not a
  globally induced embedding or a global homomorphism.

The no-singleton theorem below shows why the printed local-finiteness
condition is weaker than intended: (4b) forces C empty, so the
implication holds for ANY n, regardless of (4a) and (4c). It does
not assert that the whole paper's theorem has been formalized.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V W P : Type v}

/-- Exactly Definition 2.17(4b) with intrinsic, not closed-test,
U-irreducibility. The test vertex set is preserved exactly. -/
def LiteralUIrreduciblesIn
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (C : RelStructure L V) : Prop :=
  ∀ S : Set V,
    IsUIrreducible rules (C.induce S) →
      K (C.induce S)

/-- The literal K-valued U-completion, with the target finite and
ordinary irreducible, as in Definition 2.15. -/
def HasLiteralUKCompletion
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (C : RelStructure L V) : Prop :=
  ∃ (W : Type v) (_ : Finite W) (D : RelStructure L W),
    K D ∧ IsUCompletion rules C D

/-- Published Definition 2.17(4), at fixed B, C0 and n.
This is deliberately NOT the stronger repaired closed-test axiom. -/
def LiteralULocalCompletionAt
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (B : RelStructure L W)
    (C0 : RelStructure L P)
    (n : ℕ) : Prop :=
  ∀ {X : Type v} [Finite X] (C : RelStructure L X),
    IsUClosed rules C →
    IsUCompletion rules C C0 →
    LiteralUIrreduciblesIn K rules C →
    (∀ S : Finset X, S.card ≤ n →
      HasLiteralUKCompletion K rules (C.induce (↑S : Set X))) →
    HasCopywiseCompletion K B C

/-- The *printed* local-completion implication is automatic for a
class without one-point structures. The B-copywise conclusion
follows from (4b) alone. No assumption about C0, U-closedness
or small weak K-completions is used in the proof. -/
theorem literalULocalCompletionAt_of_noSingletons
    {K : StructureClass.{u,v} (L := L)}
    (rules : ClosureDescription L)
    (B : RelStructure L W) (C0 : RelStructure L P)
    [Finite W] (hB : K B)
    (hNoSingleton :
      ∀ {X : Type v} [Nonempty X] [Subsingleton X]
        (D : RelStructure L X), ¬ K D)
    (n : ℕ) :
    LiteralULocalCompletionAt K rules B C0 n := by
  intro X hX C _ _ hTests _
  exact copywiseCompletion_of_intrinsic_tests_mem_of_no_singletons
    B hB C hNoSingleton hTests

/-- In particular the claim holds with the nontrivial cutoff n=1,
which is the value needed for the paired-equivalence counterexample. -/
theorem literalULocalCompletionAt_one_of_noSingletons
    {K : StructureClass.{u,v} (L := L)}
    (rules : ClosureDescription L)
    (B : RelStructure L W) (C0 : RelStructure L P)
    [Finite W] (hB : K B)
    (hNoSingleton :
      ∀ {X : Type v} [Nonempty X] [Subsingleton X]
        (D : RelStructure L X), ¬ K D) :
    LiteralULocalCompletionAt K rules B C0 1 :=
  literalULocalCompletionAt_of_noSingletons rules B C0 hB hNoSingleton 1

end AllThoseRamseyClasses.Published
