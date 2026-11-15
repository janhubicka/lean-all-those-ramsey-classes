import AllThoseRamseyClasses.Published.TrackEProfileTagInternalBCover2019
import PartiteConstruction.Iterated.FinalAttachment

/-!
# Track E: actual internal B-copies descend from tagged profiles

Once a finite tagged 2019 witness Q' has genuine INTERNAL copies of the
canonical Btag extending every ordinary irreducible tagged test, every
irreducible test of the ORIGINAL relational reduct Q'old extends to
an actual original B-copy in Q'old on the EXACT same vertex set.

The reason is only full relational embedding functoriality. An OLD
irreducible test is also irreducible after adding profile and root
tags: original relation symbols remain present. A full tagged B-copy
projects to a full original B-copy on the IDENTICAL vertices.

This is the final clause (3) decoding direction. It does NOT supply
tagged internal B-extension for the second coordinated pass or justify
the optional strict FUNCTIONAL B-tree local completion condition.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Internal Btag extension on a potentially noncanonical tagged C
implies internal ORIGINAL B-extension on the same carrier C.
Only full embeddings and the literal original-language reduct are used;
no canonical representation of C or closure-hull substitution. -/
theorem profileRootTag2019_internalOriginalBCover_of_tagged
    {rules : ClosureDescription L}
    {UB X : Type v}
    (Base : RelStructure L UB)
    (C : RelStructure (profileRootTagLanguage2019 rules Base) X)
    (hTagged : IrreduciblesExtendTo
      (profileRootTagExpansion2019 rules Base
        (closureProfileExpansion2019 rules Base Base)) C) :
    IrreduciblesExtendTo Base (profileRootTagOriginal2019 Base C) := by
  intro S hIrred
  have hTaggedIrred : (C.induce S).Irreducible := by
    intro x y hxy
    obtain ⟨R, t, i, j, ht, hi, hj⟩ := hIrred hxy
    exact ⟨.inl (.inl R), t, i, j, ht, hi, hj⟩
  obtain ⟨beta, hBeta⟩ := hTagged S hTaggedIrred
  let betaOriginal : Embedding Base (profileRootTagOriginal2019 Base C) :=
    profileRootTagOriginalEmbedding2019 Base beta
  exact ⟨betaOriginal, hBeta⟩

end AllThoseRamseyClasses.Published
