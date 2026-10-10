import AllThoseRamseyClasses.Published.MatchingClosure
import PartiteConstruction.Ramsey.ClosureClosedLocalFiniteness

/-!
# Closed hereditariness of the paired-equivalence class

This proves exactly the 2019 Definition 2.17(2) condition for the
counterexample class: only U-closed embedded substructures of
a matching/equivalence structure need inherit membership.

The closure output of any input vertex must remain in the embedded
substructure. Crucially, no full ordinary hereditary hypothesis
(which would fail for a singleton) is assumed.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

private theorem edge_embedding_iff
    {U V : Type} {A : RelStructure Lang U} {B : RelStructure Lang V}
    (e : Embedding A B) (R : Symbol) (x y : U) :
    edge B R (e x) (e y) ↔ edge A R x y := by
  have ht : e ∘ ![x, y] = ![e x, e y] := by
    funext i
    fin_cases i <;> rfl
  change B.rel R ![e x, e y] ↔ A.rel R ![x, y]
  rw [← ht]
  exact e.map_rel_iff R ![x, y]

/-- A U-closed induced substructure of K belongs to K: relative
closedness forces the matching mate of every vertex to remain
in the image. The equivalence relation and order are inherited
by the full embedding. -/
theorem pairedClass_of_closed_embedding
    {U V : Type}
    (A : RelStructure Lang U) (B : RelStructure Lang V)
    (hB : pairedClass B)
    (hA : IsUClosed mateRules A)
    (e : Embedding A B) :
    pairedClass A := by
  have hBClosed : IsUClosed mateRules B :=
    pairedClass_isUClosed B hB
  have hRange : IsUSubstructure mateRules B (Set.range e) :=
    e.range_isUSubstructure hA hBClosed
  refine {
    lt_irrefl := ?_
    lt_trans := ?_
    lt_total := ?_
    equiv := ?_
    mate_irrefl := ?_
    mate_symm := ?_
    mate_total := ?_
    mate_equiv := ?_ }
  · intro x hxx
    exact hB.lt_irrefl (e x) ((edge_embedding_iff e .lt x x).mpr hxx)
  · intro x y z hxy hyz
    apply (edge_embedding_iff e .lt x z).mp
    exact hB.lt_trans (e x) (e y) (e z)
      ((edge_embedding_iff e .lt x y).mpr hxy)
      ((edge_embedding_iff e .lt y z).mpr hyz)
  · intro x y hxy
    have hne : e x ≠ e y := fun heq => hxy (e.injective heq)
    rcases hB.lt_total (e x) (e y) hne with hl | hr
    · left; exact (edge_embedding_iff e .lt x y).mp hl
    · right; exact (edge_embedding_iff e .lt y x).mp hr
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      exact (edge_embedding_iff e .equiv x x).mp (hB.equiv.refl (e x))
    · intro x y hxy
      apply (edge_embedding_iff e .equiv y x).mp
      exact hB.equiv.symm
        ((edge_embedding_iff e .equiv x y).mpr hxy)
    · intro x y z hxy hyz
      apply (edge_embedding_iff e .equiv x z).mp
      exact hB.equiv.trans
        ((edge_embedding_iff e .equiv x y).mpr hxy)
        ((edge_embedding_iff e .equiv y z).mpr hyz)
  · intro x hxx
    exact hB.mate_irrefl (e x)
      ((edge_embedding_iff e .mate x x).mpr hxx)
  · intro x y hxy
    apply (edge_embedding_iff e .mate y x).mp
    exact hB.mate_symm (e x) (e y)
      ((edge_embedding_iff e .mate x y).mpr hxy)
  · intro x
    obtain ⟨yb, hyb, hUniqueB⟩ := hB.mate_total (e x)
    have hMember : yb ∈ Set.range e := by
      have hTuple : B.rel mateRule.symbol ![e x, yb] := hyb
      have hRoot : ∀ i : Fin mateRule.rootSize,
          (![e x, yb] : Fin (Lang.arity mateRule.symbol) → V)
            (i.castLE mateRule.rootLE) ∈ Set.range e := by
        intro i
        fin_cases i
        exact ⟨x, rfl⟩
      exact hRange mateRule (by simp [mateRules]) ![e x, yb]
        hTuple hRoot (1 : Fin (Lang.arity mateRule.symbol))
    obtain ⟨y, hyImage⟩ := hMember
    refine ⟨y, ?_, ?_⟩
    · apply (edge_embedding_iff e .mate x y).mp
      change edge B .mate (e x) (e y)
      rw [hyImage]
      exact hyb
    · intro z hz
      have hbz : edge B .mate (e x) (e z) :=
        (edge_embedding_iff e .mate x z).mpr hz
      have heq : e z = yb := hUniqueB (e z) hbz
      exact e.injective (heq.trans hyImage.symm)
  · intro x y hxy
    apply (edge_embedding_iff e .equiv x y).mp
    exact hB.mate_equiv (e x) (e y)
      ((edge_embedding_iff e .mate x y).mpr hxy)

/-- Exact closed-hereditary clause of the published
(R,U)-multiamalgamation definition, not the stronger ordinary
hereditary property. -/
theorem pairedClass_closedUHereditary :
    ClosedUHereditary pairedClass mateRules := by
  intro X Y A B hB hA e
  exact pairedClass_of_closed_embedding A B hB hA e

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
