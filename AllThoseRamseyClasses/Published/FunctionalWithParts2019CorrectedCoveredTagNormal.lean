import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedWeakCanonical
import PartiteConstruction.Functional.WholeMaskCoveredTargetTagNormality2019

/-!
# Track C: actual corrected (4b) forces canonical OLD-root tag normality

Every ordinary irreducible induced weak test has a full embedding into
a canonical member of the source functional H-class, by (4b). This
witness can vary from one exact test to the next. Normality of fresh
2019 U-closure tags transfers backwards along those FULL embeddings.

For a given tag tuple or complete OLD output tuple, test precisely
its existing vertex support. Both are ordinary irreducible because
their named relational tuple spans the support. The canonical local
embedding therefore establishes the tag equivalence on that exact
support; inducing and restricting canonical full-root tags commute.

No globally fixed B-cover, source hull inflation, target amalgamation,
or extra source normalization is required.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Corrected (4b) plus U-closedness, by themselves, give exact
canonical full-root tag normality of an arbitrary tagged candidate C. -/
theorem genuineTagged2019_correctedCovered_tagNormal
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C) :
    WholeMaskTagNormal C := by
  classical
  have hLocal (S : Set V) (hIrred : (C.induce S).Irreducible) :
      WholeMaskTagNormal (C.induce S) := by
    obtain ⟨X, hX, Target, partTarget, _, _, ⟨g⟩⟩ :=
      genuineTagged2019_correctedCovered_weakIrred_canonicalTarget
        H C hClosed hCovered S hIrred
    exact (wholeMaskTagNormal_canonical
      (withPartsWholeMaskOld Target partTarget)).of_embedding g
  intro p t
  let S : Set V := Set.range t
  let ts : Fin (p.input.rootSize + p.mask.size) → S :=
    fun j => ⟨t j, ⟨j, rfl⟩⟩
  constructor
  · intro hTag
    have hIrred : (C.induce S).Irreducible :=
      relationTuple_range_irreducible C (.inr p) t hTag
    have hTagLocal : (C.induce S).rel (.inr p) ts := hTag
    have hCanLocal :
        (wholeMaskTagExpansion (wholeMaskTagReduct (C.induce S))).rel
          (.inr p) ts :=
      ((hLocal S hIrred) p ts).mp hTagLocal
    have hCanAmbientInduced :
        ((wholeMaskTagExpansion (wholeMaskTagReduct C)).induce S).rel
          (.inr p) ts :=
      (wholeMaskTagExpansion_induce_rel_iff
        (wholeMaskTagReduct C) S (.inr p) ts).mp hCanLocal
    exact hCanAmbientInduced
  · intro hCanonical
    have hOld : C.rel
        (.inl (.inr (.inr (p.input,p.mask)))) t :=
      hCanonical.1
    have hIrred : (C.induce S).Irreducible :=
      relationTuple_range_irreducible C
        (.inl (.inr (.inr (p.input,p.mask)))) t hOld
    have hCanLocal :
        (wholeMaskTagExpansion (wholeMaskTagReduct (C.induce S))).rel
          (.inr p) ts :=
      (wholeMaskTagExpansion_induce_rel_iff
        (wholeMaskTagReduct C) S (.inr p) ts).mpr hCanonical
    have hTagLocal : (C.induce S).rel (.inr p) ts :=
      ((hLocal S hIrred) p ts).mpr hCanLocal
    exact hTagLocal

end AllThoseRamseyClasses.Published
