import AllThoseRamseyClasses.Published.TrackESingletonWholeMaskNativeWeakBridge
import PartiteConstruction.Functional.OutputPartSingletonization
import PartiteConstruction.Functional.AmbientRelativeWeakFunctions

/-!
# Track E2: descend split-language ambient weak maps using old output-part masks

Output-part singletonization makes the positive weak-output law easy,
but a weak map in the split language is NOT yet a native ambient-relative
weak map of the original multivalued language. A source-undefined split
(F,q) primitive can acquire an arbitrary new value in the target. Thus
complete ORIGINAL fibres need not remain complete even when every
original output lies inside the exact weak test S.

This theorem isolates a minimal sufficient missing invariant: on each
source-defined input whose entire original fibre stays in S, every
TARGET output part already occurs in the SOURCE fibre. The split
ambient-relative full-fibre law then recovers every target vertex
because there is a source output of its part. The original positive
weak incidence law follows directly from the split positive law.

Neither source injectivity nor a reflection law at source-undefined
inputs is required. The original S and f are unchanged. No external
functions are silently made total. The theorem deliberately proves
only IsAmbientRelativeWeakHomomorphism; genuine ambient irreducible
full-copy protection, OLD-mask preservation by the actual tagged
sparse witness, and the finite-family E2 Ramsey construction remain
separate obligations.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v}

/-- A per-part singletonized ambient-relative weak map descends to the
original native multivalued language when complete original inputs
have no NEW target output parts. This is exactly the phantom-output
obstruction left open by the standalone split lemma of Track E2.

The mask condition is deliberately only one-sided (target parts ⊆
source parts) and only for fully retained nonempty source fibres;
the other inclusion follows from positive split incidence mapping. -/
theorem ambientRelativeWeakHom_of_splitOutputParts_and_noNewParts
    {V W : Type w}
    (A : FunctionalPartite.System L Parts V)
    (B : FunctionalPartite.System L Parts W)
    (S : Set V) (f : S → W)
    (hSplit : IsAmbientRelativeWeakHomomorphism
      (A.splitOutputParts).toStructure S
      (B.splitOutputParts).toStructure f)
    (hNoNewParts :
      ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S),
        (A.func F (Subtype.val ∘ xs)).Nonempty →
        (∀ z, z ∈ A.func F (Subtype.val ∘ xs) → z ∈ S) →
        B.part '' (B.func F (f ∘ xs)) ⊆
          A.part '' (A.func F (Subtype.val ∘ xs))) :
    IsAmbientRelativeWeakHomomorphism A.toStructure S B.toStructure f := by
  classical
  constructor
  · constructor
    · intro R xs hx
      exact hSplit.1.1 (ULift.up R) xs hx
    · intro F xs y hy
      have hSplitMem :
          y ∈ ((A.splitOutputParts).toStructure.weakInduce S).func
            (ULift.up F, A.part y.1) xs := ⟨hy, rfl⟩
      have hTarget := hSplit.1.2
        (ULift.up F, A.part y.1) xs y hSplitMem
      exact hTarget.1
  · intro F xs hNonempty hAll
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzSplit :
          z ∈ ((A.splitOutputParts).toStructure.weakInduce S).func
            (ULift.up F, A.part z.1) xs := ⟨hz, rfl⟩
      exact (hSplit.1.2
        (ULift.up F, A.part z.1) xs z hzSplit).1
    · intro hy
      have hPartImage :
          B.part y ∈ B.part '' (B.func F (f ∘ xs)) :=
        ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hPart⟩ :=
        hNoNewParts F xs hNonempty hAll hPartImage
      have hzNonempty :
          ((A.splitOutputParts).toStructure.func
            (ULift.up F, B.part y) (Subtype.val ∘ xs)).Nonempty :=
        ⟨z, ⟨hz, hPart⟩⟩
      have hSplitAll :
          ∀ t, t ∈ (A.splitOutputParts).toStructure.func
            (ULift.up F, B.part y) (Subtype.val ∘ xs) → t ∈ S := by
        intro t ht
        exact hAll t ht.1
      have hEq := hSplit.2
        (ULift.up F, B.part y) xs hzNonempty hSplitAll
      have hySplit :
          y ∈ (B.splitOutputParts).toStructure.func
            (ULift.up F, B.part y) (f ∘ xs) := ⟨hy, rfl⟩
      rw [← hEq] at hySplit
      obtain ⟨zS, hzSplit, hzy⟩ := hySplit
      exact ⟨zS, hzSplit.1, hzy⟩

end AllThoseRamseyClasses.Published
