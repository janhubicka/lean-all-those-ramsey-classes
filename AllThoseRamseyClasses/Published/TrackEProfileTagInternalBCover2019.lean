import AllThoseRamseyClasses.Published.ProfileRootTagTransfer2019
import PartiteConstruction.Iterated.FinalAttachment

/-!
# Track E: lift actual internal B-copies through canonical profile-root tags

The first strict 2019 profile pass already yields internal Bplus-copy
extension for each ordinary irreducible source test of its P.
The second tagged pass uses canonical Ptag and Btag controls.

On CANONICAL profile-root tag expansions, fresh tagged tuples carry
an OLD profile relation on precisely the same displayed vertices.
Thus ordinary irreducibility of an induced tagged test implies
ordinary irreducibility of its OLD profile reduct. Conversely, the
old relations remain in the tagged language so hereditary ordinary
irreducibility of the old Base propagates to the tagged Base.

Any internal full Bplus-copy beta:Bplus↪P in the old control lifts by
the existing verified profileRootTagEmbedding2019 functor to a full
Btag-copy in Ptag on the IDENTICAL map. Therefore the first pass's
actual internal Bplus-extension is inherited by the selected canonical
tagged control Ptag, without an extra coverage oracle.

These statements are for a SYNTACTICALLY CANONICAL tagged control
only. They do NOT claim internal B-coverage of the second noncanonical
tagged Q itself, or any local H-completion preservation after padding.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Any ordinarily irreducible exact induced test in a CANONICAL
profile-root tagging is also ordinarily irreducible in the old
profile structure on the SAME test carrier. Fresh tags cannot create
new Gaifman incidences unsupported by old tuples. -/
theorem profileRootTag2019_irreducible_induced_to_old
    {rules : ClosureDescription L}
    {UB X : Type v} (Base : RelStructure L UB)
    (Old : RelStructure (closureProfileLanguage2019 rules Base) X)
    (S : Set X)
    (h : ((profileRootTagExpansion2019 rules Base Old).induce S).Irreducible) :
    (Old.induce S).Irreducible := by
  intro x y hxy
  obtain ⟨R, t, i, j, ht, hi, hj⟩ := h hxy
  cases R with
  | inl R =>
      exact ⟨R, t, i, j, ht, hi, hj⟩
  | inr p =>
      exact ⟨.inl p.originalRule.symbol, t, i, j, ht.1, hi, hj⟩

/-- Hereditary ordinary irreducibility is retained by canonical
profile-root tagging, because all old profile tuples remain present. -/
theorem profileRootTag2019_hereditarilyIrreducible
    {rules : ClosureDescription L}
    {UB X : Type v} (Base : RelStructure L UB)
    (Old : RelStructure (closureProfileLanguage2019 rules Base) X)
    (hOld : HereditarilyIrreducible Old) :
    HereditarilyIrreducible
      (profileRootTagExpansion2019 rules Base Old) := by
  intro S
  have hIrr : (Old.induce S).Irreducible := hOld S
  intro x y hxy
  obtain ⟨R, t, i, j, ht, hi, hj⟩ := hIrr hxy
  exact ⟨.inl R, t, i, j, ht, hi, hj⟩

/-- In particular the exact Btag used by the coordinated 2019
construction is hereditarily ordinarily irreducible: the first
profile expansion's Bplus is already hereditarily irreducible. -/
theorem profileTaggedCanonical2019_base_hereditarilyIrreducible
    {rules : ClosureDescription L}
    {UB : Type v} (Base : RelStructure L UB)
    (hBase : IsUClosed rules Base) :
    HereditarilyIrreducible
      (profileRootTagExpansion2019 rules Base
        (closureProfileExpansion2019 rules Base Base)) :=
  profileRootTag2019_hereditarilyIrreducible Base
    (closureProfileExpansion2019 rules Base Base)
    (closureProfile2019_base_hereditarily_irreducible Base hBase)

/-- Actual INTERNAL old-profile Base-copy extension lifts to the
SAME selected canonical tagged control on the SAME vertex map.

Each tagged irreducible test S is already old-profile irreducible;
the given internal old Base-copy contains S, and tag functoriality
lifts that exact B-copy without adding vertices to S or altering
its selected map. -/
theorem profileRootTag2019_internalBCover_of_old
    {rules : ClosureDescription L}
    {UB VB VP : Type v}
    (Base : RelStructure L UB)
    (Bplus : RelStructure (closureProfileLanguage2019 rules Base) VB)
    (P : RelStructure (closureProfileLanguage2019 rules Base) VP)
    (hInternal : IrreduciblesExtendTo Bplus P) :
    IrreduciblesExtendTo
      (profileRootTagExpansion2019 rules Base Bplus)
      (profileRootTagExpansion2019 rules Base P) := by
  intro S hTagIrred
  have hOldIrred : (P.induce S).Irreducible :=
    profileRootTag2019_irreducible_induced_to_old Base P S hTagIrred
  obtain ⟨beta, hBeta⟩ := hInternal S hOldIrred
  let betaTag : Embedding
      (profileRootTagExpansion2019 rules Base Bplus)
      (profileRootTagExpansion2019 rules Base P) :=
    profileRootTagEmbedding2019 Base beta
  refine ⟨betaTag, ?_⟩
  intro z
  obtain ⟨b, hb⟩ := hBeta z
  exact ⟨b, hb⟩

end AllThoseRamseyClasses.Published
