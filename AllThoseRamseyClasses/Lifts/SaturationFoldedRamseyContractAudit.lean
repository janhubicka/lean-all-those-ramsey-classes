import AllThoseRamseyClasses.Lifts.SaturationFoldedRamseyReduction

/-!
# Validate the strength and non-vacuity of the corrected Ramsey contract

The corrected sparse-control condition only accepts an admissible
maximal-trace right pattern. Without this restriction its universal
quantifier would demand a forbidden-free target containing a forbidden
right pattern, as certified by the necessity lemma in the imported file.

We prove the EXACT converse to the existing reduction: a Ramsey target
in the age supplies a sparse control by using that very target and its
literal weak inclusions. Thus the corrected contract is EQUIVALENT to
the ordered Ramsey conclusion presently written, not an independently
proved weakening of the remaining construction problem.

Two positive consistency checks are included: any admissible right
pattern supplies its own one-colour control, and the EMPTY original
forbidden family has controls for every finite colour set by the
existing full-language ordered Ramsey theorem.

These checks neither construct the required controls for general
nonempty families nor establish the unrestricted Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe v

/-- Exact logical strength of the corrected sparse-control premise.
The reverse implication uses a genuine finite AGE Ramsey target as
its own ambient control. Its forbidden-free native shadow supplies
all literal ambient-relative weak completions by inclusion.

Consequently this equivalence must NOT be counted as an independent
construction of the missing nonempty-family Ramsey controls. -/
theorem boundedSaturationFolded_sparseControls_iff_orderedRamsey
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    BoundedSaturationFoldedSparseControls L F N ↔
      (∀ {VA VB : Type}
        [LinearOrder VA] [LinearOrder VB]
        [Finite VA] [Finite VB]
        (A : Structure (boundedSaturationFoldedLanguage L F N) VA)
        (B : Structure (boundedSaturationFoldedLanguage L F N) VB)
        (hB : IsFiniteNamedMaximalTrace
          (boundedSaturationNamedFamily L F N) B)
        (κ : Type v) [Fintype κ] [Nonempty κ],
        ∃ (VT : Type) (_ : Finite VT) (o : LinearOrder VT)
          (T : Structure (boundedSaturationFoldedLanguage L F N) VT),
          IsFiniteNamedMaximalTrace
            (boundedSaturationNamedFamily L F N) T ∧
          Structure.Arrow A.withLinearOrder B.withLinearOrder
            (@Structure.withLinearOrder _ VT T o.toLT) κ) := by
  constructor
  · intro h VA VB _ _ _ _ A B hB κ _ _
    exact boundedSaturationFolded_orderedRamsey_of_sparseControls
      L F N h A B hB κ
  · intro h VA VB _ _ _ _ A B hB κ _ _
    obtain ⟨VT, hFinT, oT, T, hT, hArrow⟩ := h A B hB κ
    letI : Finite VT := hFinT
    have hAvoid : AvoidsFiniteNamedEHN
        (boundedSaturationNamedFamily L F N)
        (FiniteNamedTraceShadow (boundedSaturationNamedFamily L F N) T) :=
      finiteNamedMaximalTraceAge_shadow_avoids
        (boundedSaturationNamedFamily L F N) hT
    exact ⟨VT, hFinT, oT, T, hArrow,
      ambientRelativeWeakCompletions_of_avoidsFiniteNamedEHN
        (boundedSaturationNamedFamily L F N)
        (FiniteNamedTraceShadow (boundedSaturationNamedFamily L F N) T)
        hAvoid N⟩

/-- Positive consistency check for NONEMPTY forbidden families as
well: an admissible marked bar itself is an ambient control whenever
all colours are equal. Membership in the age is used to construct,
not postulate, the native weak completions. -/
theorem boundedSaturationFolded_oneColourControl
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    {VA VB : Type} [LinearOrder VA] [LinearOrder VB]
    (A : Structure (boundedSaturationFoldedLanguage L F N) VA)
    (B : Structure (boundedSaturationFoldedLanguage L F N) VB)
    (hB : IsFiniteNamedMaximalTrace
      (boundedSaturationNamedFamily L F N) B)
    (κ : Type v) [Subsingleton κ] :
    ∃ (VC : Type) (_ : Finite VC) (o : LinearOrder VC)
      (C : Structure (boundedSaturationFoldedLanguage L F N) VC),
      Structure.Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder _ VC C o.toLT) κ ∧
      FiniteNamedAmbientRelativeWeakCompletions
        (boundedSaturationNamedFamily L F N)
        (FiniteNamedTraceShadow (boundedSaturationNamedFamily L F N) C) N := by
  letI : Finite VB := hB.1
  have hArrow : Structure.Arrow A.withLinearOrder B.withLinearOrder
      B.withLinearOrder κ := by
    intro χ
    refine ⟨Structure.Embedding.id _, ?_⟩
    intro e₁ e₂
    exact Subsingleton.elim _ _
  have hAvoid : AvoidsFiniteNamedEHN
      (boundedSaturationNamedFamily L F N)
      (FiniteNamedTraceShadow (boundedSaturationNamedFamily L F N) B) :=
    finiteNamedMaximalTraceAge_shadow_avoids
      (boundedSaturationNamedFamily L F N) hB
  exact ⟨VB, inferInstance, inferInstance, B, hArrow,
    ambientRelativeWeakCompletions_of_avoidsFiniteNamedEHN
      (boundedSaturationNamedFamily L F N)
      (FiniteNamedTraceShadow (boundedSaturationNamedFamily L F N) B)
      hAvoid N⟩

/-- Non-vacuity of the corrected UNIVERSAL contract: if the original
forbidden family is empty then its saturation and finite named list
are empty, so the existing ambient ordered Ramsey theorem constructs
the required controls for every finite colour set.

This is a base case, not a proof for nonempty forbidden families. -/
theorem boundedSaturationFolded_sparseControls_of_emptyFamily
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hEmpty : ∀ {W : Type} (Source : Structure L W), ¬ F Source) :
    BoundedSaturationFoldedSparseControls.{v} L F N := by
  intro VA VB _ _ _ _ A Bbar _hBbar κ _ _
  let Family := boundedSaturationNamedFamily L F N
  obtain ⟨VC, hFinC, oC, C, hArrow⟩ :=
    finiteNamedTraceAmbient_orderedRamsey Family A Bbar κ
  letI : Finite VC := hFinC
  have hAvoid : AvoidsFiniteNamedEHN Family
      (FiniteNamedTraceShadow Family C) := by
    intro i _f _hf
    have hi : FullRangeEHNSaturation F i.2.1 := i.2.2
    obtain ⟨V, Source, _hFinite, hF, _q, _hq, _hSurj⟩ := hi
    exact hEmpty Source hF
  exact ⟨VC, hFinC, oC, C, hArrow,
    ambientRelativeWeakCompletions_of_avoidsFiniteNamedEHN
      Family (FiniteNamedTraceShadow Family C) hAvoid N⟩

end AllThoseRamseyClasses.Lifts
