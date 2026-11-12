import AllThoseRamseyClasses.Published.TrackEOldSplitHybridCanonical
import PartiteConstruction.Functional.WholeMaskDomainCoherenceFreeAmalgam2019

/-!
# Track E2: the ORIGINAL output-part-mask coherence law inside hybrid pictures

The single hybrid Ramsey picture carries an old complete-output mask
domain predicate for each original function input equality pattern.
On one input, all active masks must name the SAME SET of output parts;
different enumerations of that set are harmless.

The native canonical hybrid presentation has this law, because its
OLD component is exactly the verified canonical complete-mask graph
of a genuine native Option(Set) structure. Crucially the law persists
on the SAME exact weak subset S, even if the complete output tuple
escapes S: the old active-domain relations are ambient and induced.

It also survives a genuine relational free amalgam of BASE hybrid
pictures, provided the two sides and common root satisfy the law.
This follows by forgetting to the ORIGINAL OLD complete-mask
language: full hybrid embeddings retain an exact induced OLD
embedding and free tuple localization, including cross-side
input roots. The pinned checked whole-mask domain-coherence
free-amalgam lemma then applies unchanged.

This is one important target-side normalization invariant, NOT a
proof that arbitrary hybrid pictures have complete-value witnesses,
valid split-output/root tags, a functional decoding, or class strong
amalgamation. It imposes no generated hull on a weak source.
-/

namespace StructuralRamsey.RelStructure

universe u v w z
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Forget the split-output-positive tags, outer original root tags
and unary vertex-part predicates, retaining the ORIGINAL complete-
output-part OLD domain and whole-value tuple relations exactly. -/
def splitMaskHybridOriginalOldReduct
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) :
    RelStructure (L.wholeMaskPatternLanguage Parts) V where
  rel R xs := E.rel (.inl (.inl R)) xs

/-- No active old domain relation is recomputed on an exact weak set:
the old original reduct and relational induction literally commute. -/
theorem splitMaskHybridOriginalOldReduct_induce_eq
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V)
    (S : Set V) :
    splitMaskHybridOriginalOldReduct (E.induce S) =
      (splitMaskHybridOriginalOldReduct E).induce S := rfl

/-- The actual needed target-side OLD coherence predicate:
the set of output PARTS activated by an original input does not
depend on the chosen complete mask representation/order. -/
def SplitMaskHybridOriginalDomainCoherent
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  HasUniqueWholeMaskDomainSets (splitMaskHybridOriginalOldReduct E)

/-- Every genuinely native canonical hybrid source satisfies the
original complete output-part-mask coherence law. This is NOT a
statement about an arbitrary final sparse relational picture. -/
theorem canonicalSplitMaskHybrid_originalDomainCoherent
    {V : Type w}
    (A : StructuralRamsey.FunctionalPartite.System L Parts V) :
    SplitMaskHybridOriginalDomainCoherent A.splitMaskHybrid := by
  exact StructuralRamsey.RelStructure.PartialSetStructure.wholeMaskPatternGraph_uniqueDomainSets
    A.toStructure.toNonemptyPartial A.part

/-- The original active output-PART mask coherence law is exact-
hereditary, including arbitrary nonclosed weak restrictions. -/
theorem SplitMaskHybridOriginalDomainCoherent.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : SplitMaskHybridOriginalDomainCoherent E)
    (S : Set V) :
    SplitMaskHybridOriginalDomainCoherent (E.induce S) := by
  change HasUniqueWholeMaskDomainSets
    ((splitMaskHybridOriginalOldReduct E).induce S)
  exact HasUniqueWholeMaskDomainSets.induce h S

end StructuralRamsey.RelStructure

namespace StructuralRamsey.RelStructure.Embedding

universe u v w z
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w} {W : Type z}

/-- Every full hybrid embedding induces a full ORIGINAL complete-mask
OLD relational embedding on the same map, retaining both positive
and negative domain/mask information. -/
def splitMaskHybridOriginalOldReduct
    {A : RelStructure (L.splitMaskHybrid Parts) V}
    {B : RelStructure (L.splitMaskHybrid Parts) W}
    (e : Embedding A B) :
    Embedding
      (RelStructure.splitMaskHybridOriginalOldReduct A)
      (RelStructure.splitMaskHybridOriginalOldReduct B) where
  toFun := e
  injective := e.injective
  map_rel_iff R xs := e.map_rel_iff (.inl (.inl R)) xs

end StructuralRamsey.RelStructure.Embedding

namespace StructuralRamsey.RelStructure.IsFreeAmalgam

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {H E F C : Type w}

/-- Genuine free amalgamation in the whole BASE hybrid relational
language projects to a genuine free amalgamation diagram of its
ORIGINAL OLD complete-output-mask reduct, on identical vertices. -/
theorem splitMaskHybridOriginalOldReduct
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) :
    IsFreeAmalgam
      sL.splitMaskHybridOriginalOldReduct
      sR.splitMaskHybridOriginalOldReduct
      iL.splitMaskHybridOriginalOldReduct
      iR.splitMaskHybridOriginalOldReduct where
  covers := hFree.covers
  overlap := hFree.overlap
  rel_iff R xs := hFree.rel_iff (.inl (.inl R)) xs

/-- Exactly the pinned complete-output-mask domain-coherence
free-amalgam theorem, applied to the actual original OLD reduct
of ONE base hybrid relational free diagram. Mixed original
domain masks on an input shared by two sides agree already in
the common root; no source map injection beyond the full side
embeddings is needed. -/
theorem splitMaskHybridOriginalDomainCoherent
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hRoot : SplitMaskHybridOriginalDomainCoherent Root)
    (hLeft : SplitMaskHybridOriginalDomainCoherent Left)
    (hRight : SplitMaskHybridOriginalDomainCoherent Right) :
    SplitMaskHybridOriginalDomainCoherent Whole := by
  exact (hFree.splitMaskHybridOriginalOldReduct).wholeMaskDomainSetsCoherent
    hRoot hLeft hRight

end StructuralRamsey.RelStructure.IsFreeAmalgam
