import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceAuxiliaryFreeAmalgam
import PartiteConstruction.Structure.FreeAmalgamationClass
import PartiteConstruction.Ramsey.FreeAmalgamationFunctionsAllArity

/-!
# An actual free-amalgamation Ramsey class of orphan-tolerant incidence rules

This module deliberately separates the THREE distinct problems in
the paper's totally ordered relations application:

* Local incidence-function rules, allowing orphan New_r tags, are
  inherited under full embeddings and are stable under true
  functional free amalgams.
* Consequently the class of ALL (possibly orphan-containing)
  marked structures satisfying JUST those local rules is a
  genuine free-amalgamation class. By the general functional
  EHN theorem, it is Ramsey after adding an ARBITRARY EXTERNAL
  linear order.
* The manuscript thm:TO, however, uses the INTERNAL order
  on the old and new vertices, with Old first and New_r tags
  ordered by positive tuple orders. No theorem below identifies
  an arbitrary external order with this prescribed internal one.
  The class of structures whose INTERNAL binary order relation
  is total is not itself free-amalgamation closed.

Thus the verified endpoint below is real class-level Ramsey for
a useful functional AUXILIARY class, not a proof of thm:TO.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- Full embeddings reflect all local incidence-function laws.
Equality of complete function fibres (not merely a positive
function-graph homomorphism) reconstructs a unique singleton
output in the source, including its precise new-symbol sort. -/
theorem IncidenceFunctionLaws.of_embedding
    {L : RelLanguage.{u}}
    {U V : Type v}
    {A : Structure (markedIncidencePaperLanguage L) U}
    {B : Structure (markedIncidencePaperLanguage L) V}
    (hB : IncidenceFunctionLaws B)
    (e : Structure.Embedding A B) :
    IncidenceFunctionLaws A := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro r t hPos i
    have hBpos : B.rel (.paper (.original r)) (e ∘ t) :=
      (e.map_rel_iff (.paper (.original r)) t).mpr hPos
    have hOldB := hB.positive_old r (e ∘ t) hBpos i
    have hUnary : (e ∘ ![t i]) = ![e (t i)] := by
      funext j
      fin_cases j
      rfl
    have hOldMapped : B.rel .old (e ∘ ![t i]) := by
      rw [hUnary]
      exact hOldB
    exact (e.map_rel_iff (.old) ![t i]).mp hOldMapped
  · intro r t hPos
    have hBpos : B.rel (.paper (.original r)) (e ∘ t) :=
      (e.map_rel_iff (.paper (.original r)) t).mpr hPos
    obtain ⟨z, hz, hTagB⟩ :=
      hB.positive_singleton r (e ∘ t) hBpos
    have hMap := e.map_func r t
    have hzB : z ∈ B.func r (e ∘ t) := by
      rw [hz]
      exact Set.mem_singleton z
    have hzImage : z ∈ e '' A.func r t := by
      change imageSet e (A.func r t) = B.func r (e ∘ t) at hMap
      rw [hMap]
      exact hzB
    obtain ⟨x, hx, hxeq⟩ := hzImage
    refine ⟨x, ?_, ?_⟩
    · ext y
      constructor
      · intro hy
        have hey : e y ∈ e '' A.func r t := ⟨y, hy, rfl⟩
        change e y ∈ imageSet e (A.func r t) at hey
        rw [e.map_func r t, hz] at hey
        have hyz : e y = z := by
          simpa only [Set.mem_singleton_iff] using hey
        exact e.injective (hyz.trans hxeq.symm)
      · intro hy
        have hxy : y = x := by simpa using hy
        subst y
        exact hx
    · have hUnary : (e ∘ ![x]) = ![e x] := by
        funext j
        fin_cases j
        rfl
      apply (e.map_rel_iff (.newSymbol r) ![x]).mp
      rw [hUnary, hxeq]
      exact hTagB
  · intro r t hNeg
    have hBneg : ¬ B.rel (.paper (.original r)) (e ∘ t) := by
      intro hBpos
      exact hNeg ((e.map_rel_iff (.paper (.original r)) t).mp hBpos)
    have hEmpty := hB.negative_empty r (e ∘ t) hBneg
    ext x
    constructor
    · intro hx
      have hImage : e x ∈ e '' A.func r t := ⟨x, hx, rfl⟩
      change e x ∈ imageSet e (A.func r t) at hImage
      rw [e.map_func r t, hEmpty] at hImage
      cases hImage
    · intro hx
      cases hx

/-- The actual class of ALL marked structures satisfying the
orphan-tolerant local incidence rules. An internally total order
is NOT required by this class. -/
def incidenceLawsClass
    (L : RelLanguage.{u}) :
    Structure.StructureClass.{u,v} (L := markedIncidencePaperLanguage L) :=
  fun C => IncidenceFunctionLaws C

/-- Hereditary under every FULL functional embedding and closed
under every genuine functional free amalgam, with exact output
set equality and without disallowing orphan tag vertices. -/
theorem incidenceLawsClass_free
    (L : RelLanguage.{u}) :
    Structure.FreeAmalgamationClass (incidenceLawsClass.{u,v} L) := by
  constructor
  · intro U V A B hB e
    exact hB.of_embedding e
  · intro H E F W D A B C sA sB iA iB hA hB hfree
    exact IncidenceFunctionLaws.free_amalgam hfree hA hB

/-- Genuine class-level Ramsey for the orphan-tolerant incidence-law
AUXILIARY class with an ARBITRARY EXTERNAL linear order, by the
fully verified all-arity EHN functional theorem.
It does not impose or transfer the paper's source-matched
Old-first, symbol-first INTERNAL tuple orders. -/
theorem incidenceLawsClass_freelyOrderedRamsey
    {L : RelLanguage.{u}}
    {U V : Type v}
    (A : Structure (markedIncidencePaperLanguage L) U)
    (B : Structure (markedIncidencePaperLanguage L) V)
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (hA : IncidenceFunctionLaws A)
    (hB : IncidenceFunctionLaws B)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : Structure (markedIncidencePaperLanguage L) W),
      IncidenceFunctionLaws C ∧
        Structure.Arrow A.withLinearOrder B.withLinearOrder
          (@Structure.withLinearOrder _ W C o.toLT) κ := by
  exact StructuralRamsey.Rooted.Structure.FreeAmalgamationClass.orderedRamsey_allArity
    (incidenceLawsClass_free (L := L)) A B hA hB κ

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
