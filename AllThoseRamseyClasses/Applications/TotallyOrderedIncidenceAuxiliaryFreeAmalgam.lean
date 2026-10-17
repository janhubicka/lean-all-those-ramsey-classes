import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceAuxiliaryLaws
import PartiteConstruction.Structure.FreeAmalgam

/-!
# Incidence function laws under true full functional free amalgamation

The paper's incidence-lift Ramsey application must not use the
literal canonical lift class as though it were closed-hereditary:
function-closed subsets can contain orphan relation-tag vertices.

The enlarged AUXILIARY law class permits these orphans.
The local exact rules (positive original R_tuples have singleton
New_r outputs; negative/mixed tuples have empty outputs; positive
roots are Old) are not only inherited under closed induction,
but are preserved by ANY genuine full FUNCTIONAL free amalgam
in the existing partite-construction interface.

Crucially this is a statement about complete set-valued functions:
the free-amalgam witnesses localize EACH output and each relation
tuple to an actual amalgam side. It is not merely a positive
relational homomorphism or a condition on old inputs alone.

This establishes the local incidence-law part of the class-level
free-amalgamation argument; the global unary sort partition and
prescribed orders are separate obligations.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v

/-- The exact orphan-tolerant incidence function rules survive
arbitrary genuine full functional free amalgamation. Neither
all tags being generated, nor any distinguished order, is assumed. -/
theorem IncidenceFunctionLaws.free_amalgam
    {L : RelLanguage.{u}}
    {H E F W : Type v}
    {D : Structure (markedIncidencePaperLanguage L) H}
    {A : Structure (markedIncidencePaperLanguage L) E}
    {B : Structure (markedIncidencePaperLanguage L) F}
    {C : Structure (markedIncidencePaperLanguage L) W}
    {fA : Structure.Embedding D A}
    {fB : Structure.Embedding D B}
    {iA : Structure.Embedding A C}
    {iB : Structure.Embedding B C}
    (hfree : IsFreeAmalgam fA fB iA iB)
    (hA : IncidenceFunctionLaws A)
    (hB : IncidenceFunctionLaws B) :
    IncidenceFunctionLaws C := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro r t hPositive i
    rcases (hfree.rel_iff (.paper (.original r)) t).mp hPositive with
      ⟨x, hX, hEq⟩ | ⟨y, hY, hEq⟩
    · subst t
      have hOld := hA.positive_old r x hX i
      simpa using (iA.map_rel_iff (.old) ![x i]).mpr hOld
    · subst t
      have hOld := hB.positive_old r y hY i
      simpa using (iB.map_rel_iff (.old) ![y i]).mpr hOld
  · intro r t hPositive
    rcases (hfree.rel_iff (.paper (.original r)) t).mp hPositive with
      ⟨x, hX, hEq⟩ | ⟨y, hY, hEq⟩
    · subst t
      obtain ⟨a, ha, hTag⟩ := hA.positive_singleton r x hX
      refine ⟨iA a, ?_, ?_⟩
      · calc
          C.func r (iA ∘ x) = iA '' A.func r x := by
            simpa only [imageSet] using (iA.map_func r x).symm
          _ = iA '' {a} := by rw [ha]
          _ = {iA a} := by simp
      · simpa using (iA.map_rel_iff (.newSymbol r) ![a]).mpr hTag
    · subst t
      obtain ⟨a, ha, hTag⟩ := hB.positive_singleton r y hY
      refine ⟨iB a, ?_, ?_⟩
      · calc
          C.func r (iB ∘ y) = iB '' B.func r y := by
            simpa only [imageSet] using (iB.map_func r y).symm
          _ = iB '' {a} := by rw [ha]
          _ = {iB a} := by simp
      · simpa using (iB.map_rel_iff (.newSymbol r) ![a]).mpr hTag
  · intro r t hNegative
    ext z
    constructor
    · intro hz
      rcases (hfree.func_iff r t z).mp hz with
        ⟨x, y, hy, ht, _⟩ | ⟨x, y, hy, ht, _⟩
      · have hAneg : ¬ A.rel (.paper (.original r)) x := by
          intro hp
          apply hNegative
          rw [ht]
          exact (iA.map_rel_iff (.paper (.original r)) x).mpr hp
        rw [hA.negative_empty r x hAneg] at hy
        cases hy
      · have hBneg : ¬ B.rel (.paper (.original r)) x := by
          intro hp
          apply hNegative
          rw [ht]
          exact (iB.map_rel_iff (.paper (.original r)) x).mpr hp
        rw [hB.negative_empty r x hBneg] at hy
        cases hy
    · intro hz
      cases hz

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
