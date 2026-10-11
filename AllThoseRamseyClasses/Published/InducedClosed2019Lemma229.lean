import AllThoseRamseyClasses.Published.InducedClosedLogicalDirection
import PartiteConstruction.Ramsey.ClosureRelativeControlRamsey

/-!
# Corrected 2019 Lemma 2.29 in the original induced-test language

The LITERAL Lemma 2.29 is refuted (Lemma229Counterexample).
The proposed replacement of its conclusion protects only substructures
which are simultaneously U-closed and intrinsically U-irreducible.
The additional relative A-copy hypothesis IS the original hypothesis
of Lemma 2.29, not a new restriction.

The native proof from partite-construction constructs the actual
disjoint-copy initial picture, performs its finite Hales--Jewett passes
over relevant A profiles, and extracts the global Ramsey arrow.
This file translates its conclusion to exact INDUCED 2019 tests,
without claiming the still-open unrestricted Lemma 2.28.

The optional A -> B embedding parameter records the nontrivial
Ramsey case. The 2019 proof explicitly discards the case where
the relevant copies do not exist as trivial.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {U V P : Type v}

/-- Corrected Lemma 2.29: the resulting C is U-closed, is Ramsey,
has a corrected Definition 2.15 projection to C0, and every exact
U-closed U-irreducible induced substructure of C embeds into B.

The control C0 may fail U-closedness. All its A-copy images are
assumed relatively U-closed, exactly as printed in Lemma 2.29. -/
theorem lemma_2_29_coordinated_induced
    {rules : ClosureDescription L}
    (A : RelStructure L U) (B : RelStructure L V)
    (C0 : RelStructure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (eAB : Embedding A B)
    (hCopies : ∀ alpha : Embedding A C0,
      IsUSubstructure rules C0 (Set.range alpha))
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : StructuralRamsey.Arrow A B C0 κ) :
    ∃ (Y : Type v) (_ : Finite Y)
      (C : StructuralRamsey.Partite.System L P Y),
      StructuralRamsey.Arrow A B C.toRelStructure κ ∧
      IsUClosed rules C.toRelStructure ∧
      IsInducedClosedUHomomorphismEmbedding rules
        C.toRelStructure C0 C.part ∧
      (∀ S : Set Y,
        IsUClosed rules (C.toRelStructure.induce S) →
        IsUIrreducible rules (C.toRelStructure.induce S) →
        Nonempty (Embedding (C.toRelStructure.induce S) B)) := by
  obtain ⟨Y, hY, C, hArrowC, hClosed, hProjection, hCoverage⟩ :=
    StructuralRamsey.Partite.Induced.closed_ramsey_of_relative_A_copies
      A B C0 hA hB eAB hCopies κ hArrow
  refine ⟨Y, hY, C, hArrowC, hClosed, IsClosedUHomomorphismEmbedding.toInducedClosed hProjection, ?_⟩
  intro S hTestClosed hTestIrred
  exact hCoverage (C.toRelStructure.induce S) hTestClosed
    hTestIrred (inclusion C.toRelStructure S)


/-- Full corrected statement of the 2019 Lemma 2.29, WITHOUT assuming
that A embeds into B. If A does not embed into B, choose C=B,
using the B-copy forced by the original Ramsey arrow as projection.
Otherwise use the actual protected partite construction above.

The only change to the printed lemma is that its projected map and
coverage quantify over U-CLOSED U-irreducible induced tests. -/
theorem lemma_2_29_coordinated_induced_full
    {rules : ClosureDescription L}
    (A : RelStructure L U) (B : RelStructure L V)
    (C0 : RelStructure L P)
    [Finite U] [Finite V] [Finite P]
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (hCopies : ∀ alpha : Embedding A C0,
      IsUSubstructure rules C0 (Set.range alpha))
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : StructuralRamsey.Arrow A B C0 κ) :
    ∃ (Y : Type v) (_ : Finite Y) (C : RelStructure L Y),
      StructuralRamsey.Arrow A B C κ ∧
      IsUClosed rules C ∧
      (∃ f : Y → P,
        IsInducedClosedUHomomorphismEmbedding rules C C0 f) ∧
      (∀ S : Set Y,
        IsUClosed rules (C.induce S) →
        IsUIrreducible rules (C.induce S) →
        Nonempty (Embedding (C.induce S) B)) := by
  classical
  by_cases hAB : Nonempty (Embedding A B)
  · obtain ⟨Y, hY, C, hRamsey, hClosed, hMap, hCover⟩ :=
      lemma_2_29_coordinated_induced
        A B C0 hA hB (Classical.choice hAB) hCopies κ hArrow
    exact ⟨Y, hY, C.toRelStructure, hRamsey, hClosed,
      ⟨C.part, hMap⟩, hCover⟩
  · obtain ⟨f⟩ :=
      StructuralRamsey.Partite.Induced.nonempty_embedding_of_arrow
        A B C0 κ hArrow
    letI : IsEmpty (Embedding A B) := ⟨fun e => hAB ⟨e⟩⟩
    refine ⟨V, inferInstance, B, StructuralRamsey.arrow_of_isEmpty,
      hB, ⟨f, IsClosedUHomomorphismEmbedding.toInducedClosed
        (f.isClosedUHomomorphismEmbedding rules)⟩, ?_⟩
    intro S _ _
    exact ⟨inclusion B S⟩

end AllThoseRamseyClasses.Published
