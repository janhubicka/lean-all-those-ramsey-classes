import AllThoseRamseyClasses.Published.MinimalRepair4b
import PartiteConstruction.Ramsey.ClosureClosedCompletionRank

/-!
# Exact weak n-vertex tests for the minimally repaired 2019 theorem

A sufficient stronger PROOF INVARIANT is that a positive map embeds
every abstract, intrinsically U-irreducible test that embeds into its
source, including nonclosed tests. This is not a change to the paper's
Definition 2.15: it is a stronger construction invariant and there is
an explicit implication to the LITERAL 2019 map condition.

Unlike the experimental closed-test protected map, there is NO
IsUClosed premise on a tested U-irreducible structure.

Once this stronger invariant is proved for closed hulls of generator
rank <= n, it passes to every original induced weak substructure of
at most n vertices, using the SAME finite K-target. This is the
previously missing exact weak-test bridge for Definition 2.17(4c).

The global higher-rank Picture construction providing these maps is
NOT claimed; its rank hypothesis is stated explicitly below.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V W : Type v}

/-- A strong proof invariant, NOT a revised manuscript definition.
Every embedded U-irreducible source test is protected, closed or not. -/
def IsFullyProtectedUHomomorphismEmbedding
    (rules : ClosureDescription L)
    (A : RelStructure L U) (B : RelStructure L V)
    (f : U → V) : Prop :=
  A.IsHomomorphism B f ∧
    ∀ {E : Type v} (Test : RelStructure L E),
      IsUIrreducible rules Test →
      ∀ e : Embedding Test A,
        ∃ g : Embedding Test B, ∀ x, g x = f (e x)

namespace IsFullyProtectedUHomomorphismEmbedding

variable {rules : ClosureDescription L}
variable {A : RelStructure L U} {B : RelStructure L V}
variable {f : U → V}

/-- Every fully protected map is a LITERAL 2019
U-homomorphism-embedding: take an induced test with its inclusion
into the source. There is no closedness assumption. -/
theorem toLiteral
    (h : IsFullyProtectedUHomomorphismEmbedding rules A B f) :
    IsUHomomorphismEmbedding rules A B f := by
  constructor
  · exact h.1
  · intro S hIrred
    exact h.2 (A.induce S) hIrred (inclusion A S)

/-- Unlike a weak source restriction that changes interpretation,
precomposition by a genuine full embedding retains ALL tests,
including nonclosed intrinsically U-irreducible ones. -/
theorem precomp_embedding
    (h : IsFullyProtectedUHomomorphismEmbedding rules A B f)
    {E : Type v} {Source : RelStructure L E}
    (e : Embedding Source A) :
    IsFullyProtectedUHomomorphismEmbedding rules Source B
      (f ∘ e) := by
  constructor
  · intro R x hx
    exact h.1 R (e ∘ x) ((e.map_rel_iff R x).mpr hx)
  · intro T Test hIrred a
    exact h.2 Test hIrred (e.comp a)

end IsFullyProtectedUHomomorphismEmbedding

/-- A K-valued completion carrying this stronger SOURCE invariant. -/
def HasFullyProtectedUKCompletion
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (A : RelStructure L U) : Prop :=
  ∃ (V : Type v) (_ : Finite V) (Target : RelStructure L V),
    K Target ∧ Target.Irreducible ∧
      ∃ f : U → V,
        IsFullyProtectedUHomomorphismEmbedding rules A Target f

namespace HasFullyProtectedUKCompletion

variable {K : StructureClass.{u,v} (L := L)}
variable {rules : ClosureDescription L}

/-- Explicitly discharge the ORIGINAL 2019 completion condition.
The finite target and its underlying map are NOT replaced. -/
theorem toLiteral
    {A : RelStructure L U}
    (h : HasFullyProtectedUKCompletion K rules A) :
    HasLiteralUKCompletion K rules A := by
  obtain ⟨W, hW, Target, hK, hIrred, f, hf⟩ := h
  exact ⟨W, hW, Target, hK, hIrred, f, hf.toLiteral⟩

/-- Restrict a completion to an EXACT weak source using a genuine
full embedding; no closure is added to the tested vertex set. -/
theorem pullback_embedding
    {A : RelStructure L U} {B : RelStructure L V}
    (h : HasFullyProtectedUKCompletion K rules B)
    (e : Embedding A B) :
    HasFullyProtectedUKCompletion K rules A := by
  obtain ⟨W, hW, Target, hK, hIrred, f, hf⟩ := h
  exact ⟨W, hW, Target, hK, hIrred,
    f ∘ e, hf.precomp_embedding e⟩

/-- Exactly the bridge from closed U-size rank to every original
weak n-vertex test in the printed Definition 2.17(4c).
The strong protected completion is the explicit hypothesis on the
closed hull, not an implicit assumption about all of C. -/
theorem of_closed_USize
    [Finite U]
    (rules : ClosureDescription L)
    (A : RelStructure L U)
    (hA : IsUClosed rules A)
    (n : ℕ)
    (hRank : ∀ (T : Set U) [Fintype T],
      IsUClosed rules (A.induce T) →
      USize rules (A.induce T) ≤ n →
      HasFullyProtectedUKCompletion K rules (A.induce T))
    (S : Finset U) (hS : S.card ≤ n) :
    HasFullyProtectedUKCompletion K rules
      (A.induce (↑S : Set U)) := by
  exact local_property_of_closed_USize rules A hA
    (fun {_} D => HasFullyProtectedUKCompletion K rules D)
    (fun _ _ e hD => hD.pullback_embedding e)
    n hRank S hS

end HasFullyProtectedUKCompletion

/-- The exact minimally corrected axiom can now be applied from a
closed generating-rank invariant, without weakening clause (4c)
to tests that are themselves U-closed. All control and coverage
hypotheses remain explicit. -/
theorem CorrectedULocalCompletionAt.of_rank_and_coverage
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (B : RelStructure L V)
    (C0 : RelStructure L W)
    (C : RelStructure L U) [Finite U]
    (n : ℕ)
    (hLocal : CorrectedULocalCompletionAt K rules B C0 n)
    (hC : IsUClosed rules C)
    (hControl : IsUCompletion rules C C0)
    (hCover : CorrectedUIrreduciblesIn K rules C)
    (hRank : ∀ (T : Set U) [Fintype T],
      IsUClosed rules (C.induce T) →
      USize rules (C.induce T) ≤ n →
      HasFullyProtectedUKCompletion K rules (C.induce T)) :
    HasCopywiseCompletion K B C := by
  apply hLocal C hC hControl hCover
  intro S hS
  exact (HasFullyProtectedUKCompletion.of_closed_USize
    rules C hC n hRank S hS).toLiteral

/-- Final coloring-transfer endpoint using the original Ramsey arrow,
the corrected (4b)-only local axiom, and the explicit construction
invariants. No proof of the construction is claimed here. -/
theorem ramsey_of_correctedLocalCompletion_rank_and_coverage
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (A : RelStructure L W) (B : RelStructure L V)
    (C0 : RelStructure L W) (C : RelStructure L U)
    [Finite U] (n : ℕ)
    (κ : Type*) [Nonempty κ]
    (hLocal : CorrectedULocalCompletionAt K rules B C0 n)
    (hC : IsUClosed rules C)
    (hControl : IsUCompletion rules C C0)
    (hCover : CorrectedUIrreduciblesIn K rules C)
    (hRank : ∀ (T : Set U) [Fintype T],
      IsUClosed rules (C.induce T) →
      USize rules (C.induce T) ≤ n →
      HasFullyProtectedUKCompletion K rules (C.induce T))
    (hArrow : StructuralRamsey.Arrow A B C κ) :
    ∃ (X : Type v) (_ : Finite X) (D : RelStructure L X),
      K D ∧ StructuralRamsey.Arrow A B D κ :=
  arrow_of_BCopywiseCompletion_inClass hArrow
    (CorrectedULocalCompletionAt.of_rank_and_coverage
      B C0 C n hLocal hC hControl hCover hRank)

end AllThoseRamseyClasses.Published
