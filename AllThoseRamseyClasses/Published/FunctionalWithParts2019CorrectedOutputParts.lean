import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedCoveredParts
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedWeakCanonical
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedCoveredValueCoherence
import PartiteConstruction.Functional.WholeMaskDecodedOutputParts2019

/-!
# Track C: corrected (4b) forces transversal genuine function outputs

A U-closed tagged candidate satisfying corrected (4b) has a unique
unary part relation at every vertex, and every ordinary irreducible
induced test embeds FULLY in some genuine canonical H target. For an
OLD complete output tuple, choose this target for EXACTLY the tuple's
support. Reflect each genuine output part label back to the candidate.

By uniqueness of the unary part predicates, this gives the original
OLD part-compatibility invariant for the recovered genuine vertex
part map, without requiring a single fixed B-cover of all tests.

Together with the Track C whole-value uniqueness theorem, the
generic verified decoder-fibre-transversality result yields true
transversal Option(Set) function outputs for the decoded candidate.
No nullary positive-output reduction or strict native B-tree theorem
is asserted. A source C may satisfy all these semantic laws without
being globally a member of the original class H.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Complete OLD output tuples assign their exact vertex-part labels,
where the vertex parts themselves are uniquely recovered from
corrected (4b), without a fixed canonical base B. -/
theorem genuineTagged2019_correctedCovered_outputPartsCompatible
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C) :
    WholeMaskOutputPartsCompatible (wholeMaskTagReduct C)
      (genuineTagged2019_correctedCoveredPart H C hClosed hCovered) := by
  classical
  intro p q t ht j
  let S : Set V := Set.range t
  have hIrred : (C.induce S).Irreducible :=
    relationTuple_range_irreducible C
      (.inl (.inr (.inr (p,q)))) t ht
  obtain ⟨X, hX, Target, targetPart, _, _, ⟨g⟩⟩ :=
    genuineTagged2019_correctedCovered_weakIrred_canonicalTarget
      H C hClosed hCovered S hIrred
  letI : Finite X := hX
  let ts : Fin (p.rootSize + q.size) → S :=
    fun k => ⟨t k, ⟨k, rfl⟩⟩
  have hB :
      ((Target.withParts targetPart).wholeMaskPatternGraph targetPart).rel
        (.inr (.inr (p,q))) (g ∘ ts) :=
    (g.map_rel_iff (.inl (.inr (.inr (p,q)))) ts).mpr ht
  have hPartB :
      targetPart (g (ts (Fin.natAdd p.rootSize j))) = q.label j :=
    hB.2.2 j
  have hUnaryB :
      (wholeMaskTagExpansion
        ((Target.withParts targetPart).wholeMaskPatternGraph targetPart)).rel
          (.inl (.inl (.inr (q.label j))))
          (g ∘ (fun _ : Fin 1 => ts (Fin.natAdd p.rootSize j))) := by
    change targetPart (g (ts (Fin.natAdd p.rootSize j))) = q.label j
    exact hPartB
  have hLocal : (C.induce S).rel
      (.inl (.inl (.inr (q.label j))))
      (fun _ : Fin 1 => ts (Fin.natAdd p.rootSize j)) :=
    (g.map_rel_iff
      (.inl (.inl (.inr (q.label j))))
      (fun _ : Fin 1 => ts (Fin.natAdd p.rootSize j))).mp hUnaryB
  let y : V := t (Fin.natAdd p.rootSize j)
  have hAmbient : WholeMaskVertexPartHolds C y (q.label j) := hLocal
  have hUnique :=
    (Classical.choose_spec
      (genuineTagged2019_correctedCovered_vertexPart_existsUnique
        H C hClosed hCovered y)).2
  exact (hUnique (q.label j) hAmbient).symm

/-- The complete-value decoder has genuinely transversal Option(Set)
outputs using the part map RECOVERED from corrected (4b), for all
positive primitive function arities. This preserves some-empty. -/
theorem genuineTagged2019_correctedCovered_decoder_fibreTransversal
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity) :
    PartialSetStructure.FibreTransversal
      ((wholeMaskTagReduct C).wholeMaskPartialDecode)
      (genuineTagged2019_correctedCoveredPart H C hClosed hCovered) := by
  have hCompatible : WholeMaskOutputPartsCompatible
      (wholeMaskTagReduct C)
      (genuineTagged2019_correctedCoveredPart H C hClosed hCovered) :=
    genuineTagged2019_correctedCovered_outputPartsCompatible
      H C hClosed hCovered
  have hUnique : HasUniqueWholeMaskValues (wholeMaskTagReduct C) :=
    genuineTagged2019_correctedCovered_uniqueCompleteValues
      H C hClosed hCovered hPos
  exact hCompatible.decoder_fibreTransversal
    (wholeMaskTagReduct C)
    (genuineTagged2019_correctedCoveredPart H C hClosed hCovered)
    hUnique

end AllThoseRamseyClasses.Published
