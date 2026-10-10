import PartiteConstruction.Ramsey.ClosureFivePairsRamsey

/-!
# Exact published Lemma 2.29: verified counterexample

The printed lemma (Hubička--Nešetřil 2019) assumes finite U-closed
A and B, finite control C0 with C0 -> (B)^A_2, and every A-copy
in C0 a relative U-substructure. It concludes the existence
of a finite U-closed Ramsey witness C which has a literal 2019
U-homomorphism-embedding C -> C0 and ALL intrinsically
U-irreducible induced substructures of C inside copies of B.

ClosureFivePairsRamsey.lean in the pinned partite-construction
repository proves the hypotheses for concrete One/Four/FivePairs,
then proves no such witness C exists. The contradiction does not
even need to assume the projection map.

This counterexample does not itself refute a revised lemma which
tests only U-CLOSED U-irreducibles, nor does it prove or refute the
proposed (4b)-only corrected Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.FourPointIntrinsicObstruction
open StructuralRamsey.RelStructure.TwoCopyIntrinsicObstruction

/-- The exact assumptions of printed Lemma 2.29 for the concrete
finite triple A=One, B=Four, C0=FivePairs. -/
theorem lemma229_explicit_assumptions :
    IsUClosed rules One ∧
    IsUClosed rules Four ∧
    StructuralRamsey.Arrow One Four FivePairs Bool ∧
    (∀ e : Embedding One FivePairs,
      IsUSubstructure rules FivePairs (Set.range e)) :=
  fivePairs_lemma229_hypotheses

/-- The existential CONCLUSION of printed Lemma 2.29 is false
for that same triple, even with its full literal projection notion. -/
theorem lemma229_explicit_conclusion_false :
    ¬ ∃ (W : Type) (_ : Finite W)
        (C : RelStructure Lang W),
        IsUClosed rules C ∧
        StructuralRamsey.Arrow One Four C Bool ∧
        AllIntrinsicUIrreducibleTestsEmbed rules C Four ∧
        (∃ f : W → (Fin 5 × Bool),
          IsUHomomorphismEmbedding rules C FivePairs f) :=
  lemma229_intrinsic_formulation_false

end AllThoseRamseyClasses.Published
