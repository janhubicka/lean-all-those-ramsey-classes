import AllThoseRamseyClasses.Applications.PaperForbiddenIrreducibles

/-!
# Arbitrary families of forbidden irreducible patterns

The paper's cor:digraphs remark includes digraphs omitting any set
of tournaments. Previous work handled a single forbidden pattern.

Here each index can have its own carrier type, and the family
may be infinite. Full embeddings reflect negative tuples.
Free amalgamation preserves avoidance because an irreducible
forbidden full copy must live entirely on one amalgamation side.
-/

namespace AllThoseRamseyClasses.Applications.ForbiddenPatterns

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}}
variable {I : Type w} {P : I → Type v}

/-- Avoid every member of a family of induced forbidden patterns. -/
def ForbFamily (K : StructureClass.{u,v} (L := L))
    (Forbidden : (i : I) → RelStructure L (P i)) :
    StructureClass.{u,v} (L := L) :=
  fun C => K C ∧ ∀ i : I, ¬ Nonempty (Embedding (Forbidden i) C)

/-- An arbitrary family of irreducible forbidden patterns is
hereditary and preserved by full free amalgamation. -/
theorem freeAmalgamation_of_irreducible_family
    {K : StructureClass.{u,v} (L := L)}
    {Forbidden : (i : I) → RelStructure L (P i)}
    (hK : FreeAmalgamationClass K)
    (hForbidden : ∀ i : I, (Forbidden i).Irreducible) :
    FreeAmalgamationClass (ForbFamily K Forbidden) := by
  refine ⟨?_, ?_⟩
  · intro U V A B hB e
    refine ⟨hK.hereditary hB.1 e, ?_⟩
    intro i ⟨f⟩
    exact hB.2 i ⟨e.comp f⟩
  · intro H E F W D A B C sA sB iA iB hA hB hFree
    refine ⟨hK.free hA.1 hB.1 hFree, ?_⟩
    intro i ⟨e⟩
    have hRangeIrred : (C.induce (Set.range e)).Irreducible :=
      (hForbidden i).range_embedding e
    rcases hFree.irreducible_side (Set.range e) hRangeIrred with
      hLeft | hRight
    · have hRange : ∀ x : P i, ∃ a : E, e x = iA a := by
        intro x
        obtain ⟨a, ha⟩ := hLeft ⟨e x, ⟨x, rfl⟩⟩
        exact ⟨a, ha⟩
      exact hA.2 i ⟨e.factorThroughRange iA hRange⟩
    · have hRange : ∀ x : P i, ∃ b : F, e x = iB b := by
        intro x
        obtain ⟨b, hb⟩ := hRight ⟨e x, ⟨x, rfl⟩⟩
        exact ⟨b, hb⟩
      exact hB.2 i ⟨e.factorThroughRange iB hRange⟩

/-- Ordered Ramsey for any family of irreducible forbidden
full-embedding patterns, with variable sizes and no finiteness
assumption on the forbidden family. -/
theorem orderedRamsey_avoiding_irreducible_family
    {K : StructureClass.{u,v} (L := L)}
    {Forbidden : (i : I) → RelStructure L (P i)}
    (hK : FreeAmalgamationClass K)
    (hForbidden : ∀ i : I, (Forbidden i).Irreducible)
    {U V : Type v} [Finite U] [Finite V]
    [LinearOrder U] [LinearOrder V]
    (A : RelStructure L U) (B : RelStructure L V)
    (hA : ForbFamily K Forbidden A)
    (hB : ForbFamily K Forbidden B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : RelStructure L W),
      ForbFamily K Forbidden C ∧
      StructuralRamsey.Arrow A.ordered B.ordered
        (@RelStructure.ordered L W C o.toLT) κ :=
  FreeAmalgamationClass.orderedRamsey
    (freeAmalgamation_of_irreducible_family hK hForbidden)
    A B hA hB κ

end AllThoseRamseyClasses.Applications.ForbiddenPatterns
