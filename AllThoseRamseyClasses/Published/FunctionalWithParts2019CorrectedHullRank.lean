import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedClosureDictionary
import PartiteConstruction.Ramsey.ClosureUSize2019
import PartiteConstruction.Ramsey.ClosureGeneratedHullRank
import PartiteConstruction.Structure.PartialSetFunctionsClosure

/-!
# Track C: exact functional generated hull equals repaired U-closure hull

For a U-closed corrected-(4b)-covered tagged C, the previous bridge
proves that a vertex subset is closed under ALL decoded genuinely
partial functions if and only if it is a relative U-substructure of C.

The two generated closure operators are intersections of exactly the
same family of subsets containing any seed G. Therefore they agree
ON THE NO-NEW-VERTEX CARRIER V, even when C is U-reducible.

This produces an exact correspondence of generating supports and,
for a finite source, the USize generator rank versus functional
GeneratedByAtMost n. The integer n is not shifted and the generated
HULL CARDINALITY is never used in place of its generator count.

The global decoded C need not belong to original class H. The
intrinsic nonclosed whole-weak versus ambient OLD induced completion
issue remains separate.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Corrected (4b) synchronizes both closure operators pointwise.
The generated functional hull from G is LITERALLY the 2019 relative
U-hull of G in C, without enlarging the seed G or using an ambient
full functional class-membership assumption. -/
theorem genuineTagged2019_functionClosure_eq_UClosureHull
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (G : Set V) :
    (wholeMaskOriginalDecode C).functionClosure G =
      UClosureHull ((L.withParts Parts).wholeMaskClosureRules Parts) C G := by
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  let A := wholeMaskOriginalDecode C
  have hBridge (Q : Set V) :
      A.IsClosed Q ↔ IsUSubstructure rules C Q :=
    genuineTagged2019_originalDecoded_closed_iff_Usubstructure
      H C hClosed hCovered hPos Q
  apply Set.Subset.antisymm
  · exact A.functionClosure_least
      ((hBridge (UClosureHull rules C G)).mpr
        (UClosureHull_isUSubstructure rules C G))
      (subset_UClosureHull rules C G)
  · exact UClosureHull_minimal rules C
      ((hBridge (A.functionClosure G)).mp
        (A.functionClosure_isClosed G))
      (A.subset_functionClosure G)

/-- A seed generates the entire original genuine partial function
structure exactly when it U-generates the tagged candidate.
The source C may be reducible, and G need not be finite. -/
theorem genuineTagged2019_generatedBy_iff_UGenerating
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (G : Set V) :
    (wholeMaskOriginalDecode C).GeneratedBy G ↔
      IsUGenerating
        ((L.withParts Parts).wholeMaskClosureRules Parts) C G := by
  change
    (wholeMaskOriginalDecode C).functionClosure G = Set.univ ↔
      UClosureHull ((L.withParts Parts).wholeMaskClosureRules Parts) C G =
        Set.univ
  rw [genuineTagged2019_functionClosure_eq_UClosureHull
    H C hClosed hCovered hPos G]

/-- Same generator-size cutoff n, including n=0 and generating
hulls that are vastly larger than n. No weak image set is replaced
by its generated hull when counting cardinalities. -/
theorem genuineTagged2019_generatedByAtMost_iff_UGeneratingAtMost
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    [Finite V] (n : ℕ) :
    (wholeMaskOriginalDecode C).GeneratedByAtMost n ↔
      ∃ G : Finset V,
        G.card ≤ n ∧
        IsUGenerating
          ((L.withParts Parts).wholeMaskClosureRules Parts)
          C (↑G : Set V) := by
  constructor
  · rintro ⟨G, hCard, hGenerate⟩
    exact ⟨G, hCard,
      (genuineTagged2019_generatedBy_iff_UGenerating
        H C hClosed hCovered hPos (↑G : Set V)).mp hGenerate⟩
  · rintro ⟨G, hCard, hUGenerate⟩
    exact ⟨G, hCard,
      (genuineTagged2019_generatedBy_iff_UGenerating
        H C hClosed hCovered hPos (↑G : Set V)).mpr hUGenerate⟩

/-- Exactly the 2019 USize bound: the decoded genuine source can be
generated by at most n vertices iff the tagged candidate has
USize ≤ n. This is independent of the size of any generated hull. -/
theorem genuineTagged2019_generatedByAtMost_iff_USize_le
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    [Fintype V] (n : ℕ) :
    (wholeMaskOriginalDecode C).GeneratedByAtMost n ↔
      USize
        ((L.withParts Parts).wholeMaskClosureRules Parts) C ≤ n := by
  classical
  constructor
  · intro h
    obtain ⟨G, hCard, hGen⟩ :=
      (genuineTagged2019_generatedByAtMost_iff_UGeneratingAtMost
        H C hClosed hCovered hPos n).mp h
    exact (USize_le_of_generating
      ((L.withParts Parts).wholeMaskClosureRules Parts) C G hGen).trans hCard
  · intro h
    obtain ⟨G, hCard, hGen⟩ :=
      USize_spec ((L.withParts Parts).wholeMaskClosureRules Parts) C
    apply (genuineTagged2019_generatedByAtMost_iff_UGeneratingAtMost
      H C hClosed hCovered hPos n).mpr
    exact ⟨G, hCard.symm ▸ h, hGen⟩

end AllThoseRamseyClasses.Published
