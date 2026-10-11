import AllThoseRamseyClasses.Published.CoordinatedRepair2019
import AllThoseRamseyClasses.Published.MinimalRepair4b
import PartiteConstruction.Ramsey.ClosureClosedCompletionRank

/-!
# Which direction does the coordinated 2019 repair strengthen?

The original paper quantifies over INDUCED substructures.
This file proves the complete logical direction in precisely that
convention, without presuming the mathematical theorem to be true.

For each original homomorphism-embedding, the new induced-closed map
predicate holds: demanding embeddings only on closed irreducibles
WEAKENS the map notion.

The corrected (4b) also weakens membership tests; and every literal
completion of an exact weak test is an induced-closed completion.
Therefore an implication whose (4a)--(4c) assumptions all use these
weaker tests is a STRONGER assertion:
InducedClosedULocalCompletionAt implies CorrectedULocalCompletionAt
at the SAME fixed cutoff, and hence the printed literal local axiom.

We distinguish this exact induced-test formulation from the abstract
embedded-test convention IsClosedUHomomorphismEmbedding in the pinned
partite-construction dependency. Every abstract protected map is an
induced protected map; every abstract-closed membership condition
implies induced-closed membership. The reverse test-transport
comparison must be established separately where required.

This module makes NO assertion that either local completion axiom
holds for any given K, or that the repaired Ramsey theorem follows.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V W P : Type v}

/-- The proposed new map notion stated exactly with the paper's
INDUCED substructures: on a source S require both U-closedness
and intrinsic U-irreducibility before demanding an embedding. -/
def IsInducedClosedUHomomorphismEmbedding
    (rules : ClosureDescription L)
    (A : RelStructure L V) (Target : RelStructure L W)
    (f : V → W) : Prop :=
  A.IsHomomorphism Target f ∧
    ∀ S : Set V,
      IsUClosed rules (A.induce S) →
      IsUIrreducible rules (A.induce S) →
      ∃ e : Embedding (A.induce S) Target,
        ∀ x, e x = f x.1

/-- The change to Definition 2.15 WEAKENS the map predicate. -/
theorem IsUHomomorphismEmbedding.toInducedClosed
    {rules : ClosureDescription L}
    {A : RelStructure L V} {Target : RelStructure L W}
    {f : V → W}
    (h : IsUHomomorphismEmbedding rules A Target f) :
    IsInducedClosedUHomomorphismEmbedding rules A Target f := by
  refine ⟨h.1, ?_⟩
  intro S _ hIrred
  exact h.embeddingOn S hIrred

/-- Abstract embedded-test protection used by the working Lean
construction also implies exact induced-test protection. No
isomorphism transfer is needed for this direction. -/
theorem IsClosedUHomomorphismEmbedding.toInducedClosed
    {rules : ClosureDescription L}
    {A : RelStructure L V} {Target : RelStructure L W}
    {f : V → W}
    (h : IsClosedUHomomorphismEmbedding rules A Target f) :
    IsInducedClosedUHomomorphismEmbedding rules A Target f := by
  refine ⟨h.1, ?_⟩
  intro S hClosed hIrred
  exact h.on_test (A.induce S) hClosed hIrred (inclusion A S)

/-- An abstract closed-test class membership condition gives the
literal *induced* closed (4b) condition. This does not claim the
reverse for arbitrary non-isomorphism-invariant class predicates. -/
theorem ClosedUIrreduciblesIn.toCorrectedInduced
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {A : RelStructure L V}
    (h : ClosedUIrreduciblesIn K rules A) :
    CorrectedUIrreduciblesIn K rules A := by
  intro S hClosed hIrred
  exact h (A.induce S) hClosed hIrred (inclusion A S)

/-- Exact K-completion using the new induced-closed map notion,
while still keeping the tested weak source and its finite target. -/
def HasInducedClosedUKCompletion
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (A : RelStructure L V) : Prop :=
  ∃ (Y : Type v) (_ : Finite Y) (Target : RelStructure L Y),
    K Target ∧ Target.Irreducible ∧
      ∃ f : V → Y,
        IsInducedClosedUHomomorphismEmbedding rules A Target f

/-- Every ORIGINAL K,U-completion is also a completion under
the weaker induced-closed definition. -/
theorem HasLiteralUKCompletion.toInducedClosed
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {A : RelStructure L V}
    (h : HasLiteralUKCompletion K rules A) :
    HasInducedClosedUKCompletion K rules A := by
  obtain ⟨Y, hY, Target, hK, hIrred, f, hf⟩ := h
  exact ⟨Y, hY, Target, hK, hIrred, f, IsUHomomorphismEmbedding.toInducedClosed hf⟩

/-- Every abstract embedded-test K,U-completion also satisfies
the weaker induced-test completion condition on the same weak source. -/
theorem HasClosedUKCompletion.toInducedClosed
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {A : RelStructure L V}
    (h : HasClosedUKCompletion K rules A) :
    HasInducedClosedUKCompletion K rules A := by
  obtain ⟨Y, hY, Target, hK, hIrred, f, hf⟩ := h
  exact ⟨Y, hY, Target, hK, hIrred, f, IsClosedUHomomorphismEmbedding.toInducedClosed hf⟩

/-- Coordinated local completion phrased literally with the paper's
induced tests. The cutoff n and quantification over ALL exact weak
substructures, including nonclosed sources, are unchanged. -/
def InducedClosedULocalCompletionAt
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (B : RelStructure L W) (C0 : RelStructure L P)
    (n : ℕ) : Prop :=
  ∀ {X : Type v} [Finite X] (C : RelStructure L X),
    IsUClosed rules C →
    (C0.Irreducible ∧ ∃ f : X → P,
      IsInducedClosedUHomomorphismEmbedding rules C C0 f) →
    CorrectedUIrreduciblesIn K rules C →
    (∀ S : Finset X, S.card ≤ n →
      HasInducedClosedUKCompletion K rules
        (C.induce (↑S : Set X))) →
    HasCopywiseCompletion K B C

/-- The coordinated locally finite implication is STRONGER
than the (4b)-only repaired implication at the SAME n.
This is the contravariant direction of the weakened antecedents. -/
theorem InducedClosedULocalCompletionAt.toCorrected4bOnly
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {B : RelStructure L W} {C0 : RelStructure L P}
    {n : ℕ}
    (h : InducedClosedULocalCompletionAt K rules B C0 n) :
    CorrectedULocalCompletionAt K rules B C0 n := by
  intro X hX C hClosed hCompletion hCovered hSmall
  obtain ⟨hC0, f, hf⟩ := hCompletion
  apply h C hClosed ⟨hC0, f, IsUHomomorphismEmbedding.toInducedClosed hf⟩ hCovered
  intro S hS
  exact HasLiteralUKCompletion.toInducedClosed (hSmall S hS)

/-- Therefore the coordinated local axiom implies the literal 2019
local axiom as well, again at the exact same cutoff. -/
theorem InducedClosedULocalCompletionAt.toLiteral
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {B : RelStructure L W} {C0 : RelStructure L P}
    {n : ℕ}
    (h : InducedClosedULocalCompletionAt K rules B C0 n) :
    LiteralULocalCompletionAt K rules B C0 n :=
  CorrectedULocalCompletionAt.toLiteral
    (InducedClosedULocalCompletionAt.toCorrected4bOnly h)

/-- The exact induced-test local implication implies the currently
used abstract embedded-test version: all three abstract hypotheses
are stronger, making its implication formally weaker. This avoids
silently treating test-carrier conventions as definitionally equal. -/
theorem InducedClosedULocalCompletionAt.toAbstractClosed
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {B : RelStructure L W} {C0 : RelStructure L P}
    {n : ℕ}
    (h : InducedClosedULocalCompletionAt K rules B C0 n) :
    ClosedULocalCompletionAt K rules B C0 n := by
  intro X hX C hClosed hControl hCovered hSmall
  obtain ⟨hC0, f, hf⟩ := hControl
  exact h C hClosed
    ⟨hC0, f, IsClosedUHomomorphismEmbedding.toInducedClosed hf⟩
    (ClosedUIrreduciblesIn.toCorrectedInduced hCovered)
    (fun S hS =>
      HasClosedUKCompletion.toInducedClosed (hSmall S hS))

end AllThoseRamseyClasses.Published
