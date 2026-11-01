import AllThoseRamseyClasses.Lifts.EHNPrintedTupleImageClosure
import AllThoseRamseyClasses.Lifts.EHNInputTestCoverageClosedRange
import AllThoseRamseyClasses.Lifts.RootCollisionFiveCycleRegression
import Mathlib.Tactic

/-!
# Track D: a closed weak-image range need not be tuple-surjective

An *actual native* two-relation language, with no function symbols.
Its forbidden source is the five-cycle with empty ternary relation.
Its ambient target is the triangle with the extra ternary tuple (0,1,2).

We certify within the native Structure API that the map
  (0,1,2,3,4) ↦ (0,1,0,1,2)
preserves ALL source relations and is vertex-surjective. The raw
target range is function-closed, and every source function-input
tuple has an irreducible full test **vacuously**, since there are no
functions. Nevertheless, the map is NOT original-partial
tuple-surjective even onto the actual full induced range:
the target has an additional ternary tuple without source preimage.

We also certify no full native C3 or C5 embedding into this target.
This module deliberately does NOT yet assert that this map is EHN on
all native irreducible tests, nor the universal tuple-image closure
of the entire forbidden family {C3,C5}. Thus the combined
full-hypothesis Section 3 counterexample still requires separate work.

The exact printed maximal-lift strong-amalgamation theorem is not
refuted by this isolated semantic regression.
-/

namespace AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Lifts.RootCollisionFiveCycle

/-- Binary symmetric graph edges and an independent ternary relation. -/
def language : Language where
  RelSymbol := Bool
  FuncSymbol := Empty
  relArity
    | false => 2
    | true => 3
  funcArity f := nomatch f

def cycle5 : Structure language (Fin 5) where
  rel
    | false, xs => cycle5Edge (xs 0) (xs 1)
    | true, _ => False
  func f := nomatch f

def triangleEmptyTernary : Structure language (Fin 3) where
  rel
    | false, xs => triangleEdge (xs 0) (xs 1)
    | true, _ => False
  func f := nomatch f

def triangleExtraTernary : Structure language (Fin 3) where
  rel
    | false, xs => triangleEdge (xs 0) (xs 1)
    | true, xs => extraTernary (xs 0) (xs 1) (xs 2)
  func f := nomatch f

/-- The finite colouring is a genuine native weak homomorphism.
This proves both positive relations, not just graph edges. -/
theorem weakColor_isWeakHomomorphism :
    cycle5.IsWeakHomomorphism triangleExtraTernary weakColor := by
  constructor
  · intro R xs hrel
    cases R with
    | false =>
      change triangleEdge (weakColor (xs 0)) (weakColor (xs 1))
      exact weakColor_preserves_edges (xs 0) (xs 1) hrel
    | true =>
      exact False.elim hrel
  · intro F
    exact Empty.elim F

/-- The map covers all three target vertices. -/
theorem weakColor_surjective : Function.Surjective weakColor := by
  intro y
  fin_cases y
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨4, by decide⟩

/-- There are no native functions, so every subset is closed. -/
theorem target_range_isClosed :
    triangleExtraTernary.IsClosed (Set.range weakColor) := by
  intro F
  exact Empty.elim F

/-- The SOURCE irreducible function-input cover is automatic here.
It does not control extra target relations. -/
theorem source_functionInputTuplesCovered :
    FunctionInputTuplesCoveredByIrreducibleTests cycle5 := by
  intro F
  exact Empty.elim F

/-- The target has a ternary tuple absent from the source. -/
theorem target_has_extra_ternary :
    triangleExtraTernary.rel true (fun i : Fin 3 => i) := by
  decide

theorem source_has_no_ternary
    (xs : Fin 3 → Fin 5) : ¬ cycle5.rel true xs := by
  intro h
  exact h

/-- Despite surjectivity, function-closed range, and global weak
positive preservation, the full native target has an additional
ternary relation tuple and is NOT a tuple-surjective image. -/
theorem weakColor_not_originalTupleSurjective :
    ¬ OriginalPartialTupleSurjective
      cycle5 triangleExtraTernary weakColor := by
  intro h
  obtain ⟨ys, hy, _⟩ :=
    h.1 true (fun i : Fin 3 => i) target_has_extra_ternary
  exact source_has_no_ternary ys hy

/-- Explicitly lift the extra ternary tuple to the *actual full*
target-induced structure on the (closed) source-image range. -/
theorem actual_induced_range_has_extra_ternary :
    (triangleExtraTernary.induce (Set.range weakColor)
      target_range_isClosed).rel true
        (fun i : Fin 3 => (⟨i, weakColor_surjective i⟩ :
          Set.range weakColor)) := by
  change extraTernary (0 : Fin 3) 1 2
  exact ⟨rfl, rfl, rfl⟩

/-- The extra ternary tuple remains in the TRUE induced image,
not just outside its vertex range. Hence even the exact closed
range and the source irreducible input cover are insufficient for
the extra tuple-surjectivity premise of the Track D image theorem. -/
theorem weakColor_not_tupleSurjective_on_inducedRange :
    ¬ OriginalPartialTupleSurjective
      cycle5
      (triangleExtraTernary.induce
        (Set.range weakColor) target_range_isClosed)
      (fun x => (⟨weakColor x, ⟨x, rfl⟩⟩ :
        Set.range weakColor)) := by
  intro h
  obtain ⟨ys, hy, _⟩ :=
    h.1 true
      (fun i : Fin 3 => (⟨i, weakColor_surjective i⟩ :
        Set.range weakColor))
      actual_induced_range_has_extra_ternary
  exact source_has_no_ternary ys hy

/-- No full native copy of the 5-cycle fits in the 3-point target. -/
theorem no_native_full_C5_embedding :
    ¬ Nonempty (Structure.Embedding cycle5 triangleExtraTernary) := by
  rintro ⟨e⟩
  exact no_injective_five_cycle_map e e.injective

/-- No full native copy of the empty-ternary triangle embeds into
the target carrying the additional ternary tuple. The required
ternary reflection fails for EVERY three-point bijection. -/
theorem no_native_full_C3_embedding :
    ¬ Nonempty
      (Structure.Embedding triangleEmptyTernary triangleExtraTernary) := by
  rintro ⟨e⟩
  obtain ⟨a, b, c, htuple⟩ :=
    every_injective_triangle_map_hits_extra_ternary e e.injective
  let xs : Fin 3 → Fin 3 := ![a, b, c]
  have hTarget : triangleExtraTernary.rel true (e ∘ xs) := by
    change extraTernary (e a) (e b) (e c)
    exact htuple
  have hSource : triangleEmptyTernary.rel true xs :=
    (e.map_rel_iff true xs).mp hTarget
  exact hSource

end AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap
