import AllThoseRamseyClasses.Published.InducedClosed2019ClassBridge
import PartiteConstruction.Ramsey.ClosureClosedCover

/-!
# Exact induced versus abstract embedded closed tests: 2019 normalization

The proposed coordinated correction to Definition 2.15 protects exactly
those induced substructures that are simultaneously intrinsically
U-closed and intrinsically U-irreducible.  The reusable library protects
abstract embedded closed irreducible test objects.

These predicates agree.  The missing nontrivial point is that an
intrinsically closed U-irreducible test, fully embedded into A,
identifies with a U-closed U-irreducible INDUCED range in A.
Neither the ambient A nor the target has to be U-closed.

The converse direction was checked earlier. The direct proofs below
normalize the closed test to its exact induced range, without
generating a closure hull or altering the weak tested vertex set.

Class-membership versions require the separately verified explicit
isomorphism-invariance predicate on K; map versions do not.
No Picture/rank increment or general Ramsey theorem is claimed here.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {V W : Type v}

/-- Converse to the already checked closed-cover theorem. Any closed
source with no nontrivial free cover by two relative U-substructures
is intrinsically U-irreducible in the EXACT 2019 sense. -/
theorem uIrreducible_of_closed_cover_2019
    {rules : ClosureDescription L} {A : RelStructure L V}
    (hA : IsUClosed rules A)
    (hCover :
      ∀ (S T : Set V),
        IsUSubstructure rules A S →
        IsUSubstructure rules A T →
        (∀ x : V, x ∈ S ∨ x ∈ T) →
        (∀ R (z : Fin (L.arity R) → V), A.rel R z →
          (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T)) →
        (∀ x : V, x ∈ S) ∨ (∀ x : V, x ∈ T)) :
    IsUIrreducible rules A := by
  intro H E F Root Left Right sL sR iL iR hLeftClosed hRightClosed hFree
  have hL : IsUSubstructure rules A (Set.range iL) :=
    iL.range_isUSubstructure hLeftClosed hA
  have hR : IsUSubstructure rules A (Set.range iR) :=
    iR.range_isUSubstructure hRightClosed hA
  have hVertices : ∀ z : V, z ∈ Set.range iL ∨ z ∈ Set.range iR := by
    intro z
    rcases hFree.covers z with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact Or.inl ⟨a, ha.symm⟩
    · exact Or.inr ⟨b, hb.symm⟩
  have hTuples :
      ∀ R (z : Fin (L.arity R) → V), A.rel R z →
        (∀ k, z k ∈ Set.range iL) ∨
        (∀ k, z k ∈ Set.range iR) := by
    intro R z hz
    rcases (hFree.rel_iff R z).mp hz with
      ⟨a, ha, heq⟩ | ⟨b, hb, heq⟩
    · exact Or.inl (fun k => ⟨a k, (congrFun heq k).symm⟩)
    · exact Or.inr (fun k => ⟨b k, (congrFun heq k).symm⟩)
  rcases hCover (Set.range iL) (Set.range iR) hL hR
      hVertices hTuples with hAllL | hAllR
  · exact Or.inl (fun z => hAllL z)
  · exact Or.inr (fun z => hAllR z)

/-- A surjective full embedding of an intrinsically U-CLOSED source
transports intrinsic U-IRREDUCIBILITY to its exact target. The
target is the isomorphic structure, not an ambient closure. -/
theorem uIrreducible_of_surjective_embedding_2019
    {rules : ClosureDescription L}
    {A : RelStructure L V} {B : RelStructure L W}
    (e : Embedding A B) (he : Function.Surjective e)
    (hA : IsUClosed rules A)
    (hIrred : IsUIrreducible rules A) :
    IsUIrreducible rules B := by
  have hB : IsUClosed rules B :=
    isUClosed_of_surjective_embedding e he hA
  apply uIrreducible_of_closed_cover_2019 hB
  intro S T hS hT hCover hTuples
  have hPreS : IsUSubstructure rules A (e ⁻¹' S) :=
    hS.preimage_embedding e
  have hPreT : IsUSubstructure rules A (e ⁻¹' T) :=
    hT.preimage_embedding e
  have hVertices : ∀ a : V, a ∈ e ⁻¹' S ∨ a ∈ e ⁻¹' T := by
    intro a
    exact hCover (e a)
  have hTuplesA :
      ∀ R (z : Fin (L.arity R) → V), A.rel R z →
        (∀ k, z k ∈ e ⁻¹' S) ∨
        (∀ k, z k ∈ e ⁻¹' T) := by
    intro R z hz
    have hzB : B.rel R (e ∘ z) :=
      (e.map_rel_iff R z).mpr hz
    exact hTuples R (e ∘ z) hzB
  rcases hIrred.closed_cover hA (e ⁻¹' S) (e ⁻¹' T)
      hPreS hPreT hVertices hTuplesA with hAllS | hAllT
  · left
    intro b
    obtain ⟨a, ha⟩ := he b
    rw [← ha]
    exact hAllS a
  · right
    intro b
    obtain ⟨a, ha⟩ := he b
    rw [← ha]
    exact hAllT a

/-- The image of an embedded intrinsically U-closed irreducible test
is itself intrinsically U-closed and irreducible as an EXACT
induced substructure, even if the ambient structure is not closed. -/
theorem closedIrreducible_exact_induced_range_2019
    {rules : ClosureDescription L}
    {Test : RelStructure L V} {A : RelStructure L W}
    (e : Embedding Test A)
    (hClosed : IsUClosed rules Test)
    (hIrred : IsUIrreducible rules Test) :
    IsUClosed rules (A.induce (Set.range e)) ∧
    IsUIrreducible rules (A.induce (Set.range e)) := by
  let g : Embedding Test (A.induce (Set.range e)) :=
    inducedRangeEmbedding e
  have hg : Function.Surjective g :=
    inducedRangeEmbedding_surjective e
  exact ⟨isUClosed_of_surjective_embedding g hg hClosed,
    uIrreducible_of_surjective_embedding_2019 g hg hClosed hIrred⟩

/-- The missing converse map-translation: every induced closed test
in Definition 2.15 yields protection on ANY abstract embedded
closed irreducible test. No K-isomorphism property is required. -/
theorem IsInducedClosedUHomomorphismEmbedding.toAbstract_2019
    {rules : ClosureDescription L}
    {A : RelStructure L V} {B : RelStructure L W}
    {f : V → W}
    (h : IsInducedClosedUHomomorphismEmbedding rules A B f) :
    IsClosedUHomomorphismEmbedding rules A B f := by
  refine ⟨h.1, ?_⟩
  intro X Test hClosed hIrred e
  let S : Set V := Set.range e
  let eRange : Embedding Test (A.induce S) :=
    inducedRangeEmbedding e
  obtain ⟨hRangeClosed, hRangeIrred⟩ :=
    closedIrreducible_exact_induced_range_2019 e hClosed hIrred
  obtain ⟨g, hg⟩ := h.2 S hRangeClosed hRangeIrred
  refine ⟨g.comp eRange, ?_⟩
  intro x
  exact hg (eRange x)

/-- Thus the exact induced-map convention in the proposed
2019 correction and the library's abstract closed-test map
convention are EQUIVALENT, not merely one-way comparable. -/
theorem inducedClosedMap_iff_abstract_2019
    {rules : ClosureDescription L}
    {A : RelStructure L V} {B : RelStructure L W}
    {f : V → W} :
    IsInducedClosedUHomomorphismEmbedding rules A B f ↔
      IsClosedUHomomorphismEmbedding rules A B f :=
  ⟨IsInducedClosedUHomomorphismEmbedding.toAbstract_2019,
   IsClosedUHomomorphismEmbedding.toInducedClosed⟩

/-- Every abstract embedded closed-test K-membership condition follows
from the original INDUCED condition once K is genuinely closed under
isomorphism. Without that hypothesis the bare Lean StructureClass
type does not validate this implication. -/
theorem correctedInducedCoverage_toAbstract_2019
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {A : RelStructure L V}
    (hIso : IsomorphismClosed2019 K)
    (h : CorrectedUIrreduciblesIn K rules A) :
    ClosedUIrreduciblesIn K rules A := by
  intro X Test hClosed hIrred e
  let S : Set V := Set.range e
  obtain ⟨hRangeClosed, hRangeIrred⟩ :=
    closedIrreducible_exact_induced_range_2019 e hClosed hIrred
  have hRangeInK : K (A.induce S) := h S hRangeClosed hRangeIrred
  exact hIso Test (A.induce S)
    (inducedRangeEmbedding e)
    (inducedRangeEmbedding_surjective e) hRangeInK

/-- Matching induced and abstract membership tests is a genuine iff
for isomorphism-closed K. -/
theorem correctedInducedCoverage_iff_abstract_2019
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {A : RelStructure L V}
    (hIso : IsomorphismClosed2019 K) :
    CorrectedUIrreduciblesIn K rules A ↔
      ClosedUIrreduciblesIn K rules A :=
  ⟨correctedInducedCoverage_toAbstract_2019 hIso,
   ClosedUIrreduciblesIn.toCorrectedInduced⟩

/-- Existential K-completions of arbitrary weak sources use the
SAME finite target in both map conventions; no extra class property
or closure hull is needed. -/
theorem inducedClosedKCompletion_iff_abstract_2019
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {A : RelStructure L V} :
    HasInducedClosedUKCompletion K rules A ↔
      HasClosedUKCompletion K rules A := by
  constructor
  · rintro ⟨X, hX, Target, hK, hIrred, f, hf⟩
    exact ⟨X, hX, Target, hK, hIrred, f,
      IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hf⟩
  · exact HasClosedUKCompletion.toInducedClosed

/-- A LOCAL COMPLETION AXIOM at the SAME B,C0,n agrees in the
two conventions for classes closed under isomorphism. This includes
all exact weak tests in (4c) and does not require C0 closed. -/
theorem inducedClosedLocalCompletion_iff_abstract_2019
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {B : RelStructure L V} {C0 : RelStructure L W}
    {n : ℕ}
    (hIso : IsomorphismClosed2019 K) :
    InducedClosedULocalCompletionAt K rules B C0 n ↔
      ClosedULocalCompletionAt K rules B C0 n := by
  constructor
  · exact InducedClosedULocalCompletionAt.toAbstractClosed
  · intro hAbstract X hX C hClosed hControl hCovered hSmall
    obtain ⟨hC0, f, hf⟩ := hControl
    apply hAbstract C hClosed
      ⟨hC0, f,
        IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hf⟩
      (correctedInducedCoverage_toAbstract_2019 hIso hCovered)
    intro S hS
    exact (inducedClosedKCompletion_iff_abstract_2019).mp
      (hSmall S hS)

end AllThoseRamseyClasses.Published
