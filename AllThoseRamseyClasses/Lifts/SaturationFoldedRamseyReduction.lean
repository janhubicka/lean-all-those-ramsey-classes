import AllThoseRamseyClasses.Lifts.SaturationFiniteNamedTransfer
import AllThoseRamseyClasses.Lifts.FiniteFamilyOrderedBarCertificate
import AllThoseRamseyClasses.Lifts.FiniteFamilyLocalMarkedRamseyEndgame
import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceRamseyControl

/-!
# Ramsey endgame for the bounded saturated finite-family folded expansion

The parent branch constructs an actual finite named list of all full
isomorphism representatives of the full-range EHN saturation. Its
hereditary all-closed-component maximal-trace age has the EXACT old
shadow Forb_EHN(F), finite fibres and strong amalgamation, and JEP
under connectedness and positive native arities.

Here we remove ALL auxiliary selected-bar/witness/compatible-order
choices and the source-size-cutoff choice from the ordered Ramsey
endgame. Only ONE genuine E2 construction remains: for each pair of
finite ordered patterns in the full folded language, exhibit an
ambient ordered Ramsey control C with the actual finite-size
ambient-relative weak completions of its literal native subsets.

This is explicitly a CONDITIONAL theorem. The hSparseControl
assumption is not supplied by the ambient free-amalgamation Ramsey
theorem, which yields an arrow without the needed native avoidance
condition. We do not claim that strong AP alone implies Ramsey.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe v

/-- The precise extra sparse-control existence statement missing
from the finite-family Ramsey proof. The ambient Ramsey control is
in the full folded LANGUAGE and need not initially be in the age.
It must satisfy the *exact ambient-relative* weak test completion
condition at the uniform forbidden-source size cutoff N.

CRITICAL: Bbar MUST already belong to the hereditary maximal-trace
age. If we quantified over arbitrary forbidden Bbar, the premise
would be inconsistent: an Arrow to Bbar supplies a full copy in C,
whereas local completion forces C's shadow to avoid all forbidden
sources. The requirement is exactly for the admissible marked bar
produced by the existing finite-family maximal-witness theorem.

This predicate does not postulate a maximal-trace Ramsey target.
It postulates an ambient control plus the local E2 invariant;
constructing such controls is the unsolved Ramsey step. -/
def BoundedSaturationFoldedSparseControls
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol] : Prop :=
  ∀ {VA VB : Type}
    [LinearOrder VA] [LinearOrder VB]
    [Finite VA] [Finite VB]
    (A : Structure (boundedSaturationFoldedLanguage L F N) VA)
    (Bbar : Structure (boundedSaturationFoldedLanguage L F N) VB)
    (hBbar : IsFiniteNamedMaximalTrace
      (boundedSaturationNamedFamily L F N) Bbar)
    (κ : Type v) [Fintype κ] [Nonempty κ],
    ∃ (VC : Type) (_ : Finite VC) (o : LinearOrder VC)
      (C : Structure (boundedSaturationFoldedLanguage L F N) VC),
      Structure.Arrow A.withLinearOrder Bbar.withLinearOrder
        (@Structure.withLinearOrder _ VC C o.toLT) κ ∧
      FiniteNamedAmbientRelativeWeakCompletions
        (boundedSaturationNamedFamily L F N)
        (FiniteNamedTraceShadow
          (boundedSaturationNamedFamily L F N) C) N

/-- The full bounded saturated folded age is ORDERED RAMSEY under
the one explicit ambient relative sparse-control construction.
Its target is a REAL finite age member, with a chosen external
linear order and the genuine full-embedding Ramsey arrow.

The marked Bbar, its compatible total order, the native full
maximizing W witness, its precise tag-profile reflection, and
the universal source-size cutoff are CONSTRUCTED, not assumed.
The sole unproved mathematical input remains hSparseControl. -/
theorem boundedSaturationFolded_orderedRamsey_of_sparseControls
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hSparseControl : BoundedSaturationFoldedSparseControls L F N)
    {VA VB : Type}
    [LinearOrder VA] [LinearOrder VB]
    [Finite VA]
    (A : Structure (boundedSaturationFoldedLanguage L F N) VA)
    (B : Structure (boundedSaturationFoldedLanguage L F N) VB)
    (hB : IsFiniteNamedMaximalTrace
      (boundedSaturationNamedFamily L F N) B)
    (κ : Type v) [Fintype κ] [Nonempty κ] :
    ∃ (VT : Type) (_ : Finite VT) (o : LinearOrder VT)
      (T : Structure (boundedSaturationFoldedLanguage L F N) VT),
      IsFiniteNamedMaximalTrace
        (boundedSaturationNamedFamily L F N) T ∧
      Structure.Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder _ VT T o.toLT) κ := by
  classical
  let Family := boundedSaturationNamedFamily L F N
  obtain ⟨VW, hFinW, W, Bbar, oW,
      _hAvoid, hBar, hShadow, iW, hMax, hProfile,
      mark, hMark⟩ :=
    finiteNamedTrace_exists_orderedBarWithProfile Family B hB
  letI : Finite VW := hFinW
  letI : LinearOrder VW := oW
  obtain ⟨VC, hFinC, oC, C, hArrow, hLocal⟩ :=
    hSparseControl A Bbar hBar κ
  letI : Finite VC := hFinC
  letI : LinearOrder VC := oC
  let wBar : Structure.Embedding W
      (FiniteNamedTraceShadow Family Bbar) := {
    toFun := id
    injective := Function.injective_id
    map_rel_iff := by
      intro R xs
      rw [hShadow]
      exact Iff.rfl
    map_func := by
      intro G xs
      rw [hShadow]
      exact (Structure.Embedding.id W).map_func G xs
  }
  have hMarkAligned : ∀ x : VB, wBar (iW x) = mark x := by
    intro x
    change iW x = mark x
    exact (hMark x).symm
  have hBound :
      ∀ i : Family.Index, Nat.card (Family.Carrier i) ≤ N := by
    intro i
    change Nat.card (Fin i.1.1) ≤ N
    simpa only [Nat.card_fin] using
      (Nat.le_of_lt_succ i.1.2)
  exact finiteNamedMarkedWitnessRamsey_of_localCompletions
    Family A B Bbar C W iW hMax hProfile
    mark wBar hMarkAligned hArrow N hBound hLocal

end AllThoseRamseyClasses.Lifts
