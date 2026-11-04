import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedWeakCanonical
import PartiteConstruction.Functional.WholeMaskCoveredDefinedEmpty2019

/-!
# Track C: corrected (4b) supplies complete defined-empty OLD graph records

A zero-output OLD domain mask is NOT an undefined function state.
Under the 2019 corrected closed-test coverage clause (4b), its exact
input-root tuple support is ordinarily irreducible and hence embeds
FULLY into SOME genuine canonical H-target, by the already checked
weak-irreducible canonical-target lemma.

In that genuine target a zero-output mask means a real SOME-EMPTY
function value; therefore the corresponding zero-output complete OLD
graph tuple holds. Reflect that tuple through the full embedding on
the exact root carrier. No fixed B-cover, change to the tested carrier,
target enlargement, or hidden local-axiom oracle is required.

This is a new normalization ingredient for arbitrary corrected
U-closed (4b)-covered candidates, complementary to value uniqueness.
-/ 

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Under the ACTUAL corrected (4b) class membership condition,
every active defined-empty OLD domain produces its complete empty
output tuple on exactly the original input-root vertices.

Unlike the earlier B-covered version, each test may embed into
a DIFFERENT genuine H target; the reflection is still sufficient. -/
theorem genuineTagged2019_correctedCovered_definedEmpty_has_completeGraph
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (p : Language.FunctionInputPattern (L.withParts Parts))
    (q : Language.CompleteOutputParts Parts)
    (hq : q.size = 0)
    (root : Fin p.rootSize → V)
    (hDom : (wholeMaskTagReduct C).rel
      (.inr (.inl (p,q))) root) :
    ∃ t : Fin (p.rootSize + q.size) → V,
      (wholeMaskTagReduct C).rel (.inr (.inr (p,q))) t ∧
      ∀ i : Fin p.rootSize,
        t (Fin.castAdd q.size i) = root i := by
  classical
  let S : Set V := Set.range root
  have hIrred : (C.induce S).Irreducible :=
    relationTuple_range_irreducible C
      (.inl (.inr (.inl (p,q)))) root hDom
  obtain ⟨X, hX, Target, targetPart, _, _, ⟨g⟩⟩ :=
    genuineTagged2019_correctedCovered_weakIrred_canonicalTarget
      H C hClosed hCovered S hIrred
  letI : Finite X := hX
  let B := Target.withParts targetPart
  let rootS : Fin p.rootSize → S :=
    fun i => ⟨root i, ⟨i, rfl⟩⟩
  have hDomB : (B.wholeMaskPatternGraph targetPart).rel
      (.inr (.inl (p,q))) (g ∘ rootS) :=
    (g.map_rel_iff (.inl (.inr (.inl (p,q)))) rootS).mpr hDom
  obtain ⟨hInjB, U, hValueB, hMaskB⟩ := hDomB
  have hMaskEmpty : Set.range q.label = (∅ : Set Parts) := by
    ext a
    constructor
    · rintro ⟨j, _⟩
      exact False.elim (completeOutputParts_zero_no_index q hq j)
    · intro ha
      exact ha.elim
  have hUEmpty : U = ∅ := by
    ext y
    constructor
    · intro hy
      have hPart : targetPart y ∈ Set.range q.label := by
        rw [← hMaskB]
        exact ⟨y, hy, rfl⟩
      rw [hMaskEmpty] at hPart
      exact hPart.elim
    · intro hy
      exact hy.elim
  have hValueEmpty :
      B.func p.symbol ((g ∘ rootS) ∘ p.argMap) = some (∅ : Set X) := by
    rw [hUEmpty] at hValueB
    exact hValueB
  let tS : Fin (p.rootSize + q.size) → S :=
    Fin.append rootS
      (fun j : Fin q.size =>
        False.elim (completeOutputParts_zero_no_index q hq j))
  have hInput : (fun i : Fin p.rootSize =>
      (g ∘ tS) (Fin.castAdd q.size i)) = g ∘ rootS := by
    funext i
    simp only [Function.comp_apply, tS, Fin.append_left]
  have hOutputEmpty : Set.range (fun j : Fin q.size =>
      (g ∘ tS) (Fin.natAdd p.rootSize j)) = (∅ : Set X) := by
    ext y
    constructor
    · rintro ⟨j, _⟩
      exact False.elim (completeOutputParts_zero_no_index q hq j)
    · intro hy
      exact hy.elim
  have hGraphB : (B.wholeMaskPatternGraph targetPart).rel
      (.inr (.inr (p,q))) (g ∘ tS) := by
    change Function.Injective (fun i : Fin p.rootSize =>
        (g ∘ tS) (Fin.castAdd q.size i)) ∧
      B.func p.symbol
        ((fun i : Fin p.rootSize =>
          (g ∘ tS) (Fin.castAdd q.size i)) ∘ p.argMap) =
        some (Set.range (fun j : Fin q.size =>
          (g ∘ tS) (Fin.natAdd p.rootSize j))) ∧
      (∀ j : Fin q.size,
        targetPart ((g ∘ tS) (Fin.natAdd p.rootSize j)) = q.label j)
    constructor
    · rw [hInput]
      exact hInjB
    constructor
    · rw [hInput, hOutputEmpty]
      exact hValueEmpty
    · intro j
      exact False.elim (completeOutputParts_zero_no_index q hq j)
  have hLocal : (C.induce S).rel
      (.inl (.inr (.inr (p,q)))) tS :=
    (g.map_rel_iff (.inl (.inr (.inr (p,q)))) tS).mp hGraphB
  refine ⟨Subtype.val ∘ tS, hLocal, ?_⟩
  intro i
  simp only [Function.comp_apply, tS, Fin.append_left, rootS]

end AllThoseRamseyClasses.Published
