import AllThoseRamseyClasses.Published.TrackESplitSingletonPositiveRelativeWeak
import AllThoseRamseyClasses.Published.TrackEOldDomainMaskExactParts
import AllThoseRamseyClasses.Published.TrackESplitWeakHomOriginalMaskBridge
import PartiteConstruction.Functional.WholeMaskCanonicalFullEmbeddingForward2019
import PartiteConstruction.Functional.WholeMaskClosureSemiClosed2019
import PartiteConstruction.Functional.PatternClosureTags2019
import PartiteConstruction.Functional.OutputPartSingletonization

/-!
# Track E2: a single canonical relational presentation with split positive incidences and original OLD masks

The original corrected 2019 sparse witness uses COMPLETE output-value
mask symbols, which do not record clipped positive incidences on exact
weak tests. A singletonized pattern graph retains every such incidence,
but without the original mask can add phantom output parts in a target.

We define one finite-signature candidate HYBRID source language:
* the original complete-value OLD tag relations (whole output-part
  masks, active domains, and their original full-root tags);
* the per-output-part singleton equality-pattern OLD/tag relations;
* one unary vertex-part predicate for every part, including isolated
  vertices.

A real native FunctionalPartite.System has a canonical hybrid
presentation on exactly its ORIGINAL vertex carrier. Every full native
part-preserving embedding induces a FULL hybrid induced embedding,
using the independently verified two canonical embedding functors.

On arbitrary exact weak S, a SINGLE POSITIVE relational homomorphism
between two such canonical hybrid sources projects, ON THE SAME f,
to both the singleton split-pattern positive map and the complete
original output-PART mask map. The new singleton-target bridge plus
the earlier merged OLD-mask descent then yield an actual original
native ambient-relative WEAK HOMOMORPHISM, preserving every
vertex's part label (even if otherwise isolated).

This is still NOT a hybrid Ramsey sparsening or target completion:
arbitrary relational intermediate hybrid pictures need not be
canonical/decodable; hybrid closure roots, strong/free amalgamation
and protected full irreducible copies remain to be established.
The conclusion deliberately does NOT assert IsAmbientRelativeWeakHE.
-/

namespace StructuralRamsey.Language

universe u v

/-- One exact carrier with both canonical tagged function encodings
and explicit unary vertex parts. The sum is syntactic: no
arbitrary hybrid relational structure is assumed to decode into
a coherent native functional System. -/
def splitMaskHybrid
    (L : Language.{u}) (P : Type v) [Fintype P] :
    RelLanguage.{max u v} where
  Symbol :=
    (L.wholeMaskTagLanguage P).Symbol ⊕
      (((L.outputPartIndexed P).patternTag).Symbol ⊕ P)
  arity
    | .inl R => (L.wholeMaskTagLanguage P).arity R
    | .inr (.inl R) => ((L.outputPartIndexed P).patternTag).arity R
    | .inr (.inr _) => 1

end StructuralRamsey.Language

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {P : Type v} [Fintype P]
variable {V : Type w}

/-- Canonical same-carrier hybrid of both OLD full mask tags, positive
split-function singleton root tags and all vertex-part predicates. -/
def System.splitMaskHybrid (A : System L P V) :
    RelStructure (L.splitMaskHybrid P) V where
  rel
    | .inl R, xs =>
        (wholeMaskTagExpansion
          (A.toStructure.toNonemptyPartial.wholeMaskPatternGraph A.part)).rel R xs
    | .inr (.inl R), xs =>
        (patternTagExpansion
          A.splitOutputParts.toStructure.patternGraph).rel R xs
    | .inr (.inr q), xs =>
        A.part (xs (0 : Fin 1)) = q

end StructuralRamsey.FunctionalPartite

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Every genuine full native part-preserving embedding becomes a
FULL hybrid induced relational embedding, ON THE IDENTICAL VERTEX
MAP. The left full-mask part uses exact native Option(Set) domain
reflection; the right split part uses the canonical pattern/root
embedding functor; unary predicates retain isolated parts. -/
noncomputable def systemEmbedding_splitMaskHybrid
    {V W : Type w}
    {A : FunctionalPartite.System L Parts V}
    {B : FunctionalPartite.System L Parts W}
    (e : FunctionalPartite.Embedding A B) :
    RelStructure.Embedding A.splitMaskHybrid B.splitMaskHybrid where
  toFun := e
  injective := e.toEmbedding.injective
  map_rel_iff := by
    classical
    let ePartial : PartialSetStructure.Embedding
        A.toStructure.toNonemptyPartial
        B.toStructure.toNonemptyPartial :=
      e.toEmbedding.toNonemptyPartial
    let eOld : RelStructure.Embedding
        (A.toStructure.toNonemptyPartial.wholeMaskPatternGraph A.part)
        (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part) :=
      ePartial.wholeMaskPatternGraph A.part B.part e.map_part
    let eOldTag := eOld.wholeMaskTag
    let eSplitTag :=
      (e.splitOutputParts.toEmbedding.patternGraph).patternTag
    intro symbol xs
    rcases symbol with R | R
    · exact eOldTag.map_rel_iff R xs
    · rcases R with R | q
      · exact eSplitTag.map_rel_iff R xs
      · change (B.part (e (xs (0 : Fin 1))) = q) ↔
          (A.part (xs (0 : Fin 1)) = q)
        rw [e.map_part]

/-- One positive hybrid relational map on the SAME original exact
weak S and SAME vertex map f yields the original native
ambient-relative weak HOMOMORPHISM and preservation of vertex parts.

The proof extracts two distinct positive relations from the single
hybrid source: singleton split output graphs give all surviving
weak incidences and complete retained split fibres (by target
singleton-valuedness); original active OLD masks prevent phantom
target output parts when recombining the multivalued fibres.

No closure hull, source/target domain reflection at undefined inputs,
new vertices or independent choice of completion maps. Full
ambient-irreducible test protection is a separate HE obligation. -/
theorem nativeAmbientRelativeWeakHom_of_positiveHybridMap
    {V W : Type w} [Finite V]
    (A : FunctionalPartite.System L Parts V)
    (B : FunctionalPartite.System L Parts W)
    (S : Set V) (f : S → W)
    (hHybrid : (A.splitMaskHybrid.induce S).IsHomomorphism
      B.splitMaskHybrid f) :
    IsAmbientRelativeWeakHomomorphism
      A.toStructure S B.toStructure f ∧
    (∀ x : S, B.part (f x) = A.part x.1) := by
  have hSplit :
      ((patternTagExpansion
        A.splitOutputParts.toStructure.patternGraph).induce S).IsHomomorphism
        (patternTagExpansion
          B.splitOutputParts.toStructure.patternGraph) f := by
    intro R xs hR
    exact hHybrid (.inr (.inl R)) xs hR
  have hSplitWeak : IsAmbientRelativeWeakHomomorphism
      A.splitOutputParts.toStructure S
      B.splitOutputParts.toStructure f :=
    splitAmbientRelativeWeakHom_of_positivePatternTaggedHom
      A B S f hSplit
  have hMask :
      ∀ (p : Language.FunctionInputPattern L)
        (q : Language.CompleteOutputParts Parts)
        (rootS : Fin p.rootSize → S),
        ((A.toStructure.toNonemptyPartial.wholeMaskPatternGraph A.part).induce S).rel
          (.inr (.inl (p, q))) rootS →
        (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part).rel
          (.inr (.inl (p, q))) (f ∘ rootS) := by
    intro p q rootS hR
    exact hHybrid (.inl (.inl (.inr (.inl (p, q))))) rootS hR
  have hNoNewParts :
      ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S),
        (A.func F (Subtype.val ∘ xs)).Nonempty →
        (∀ z, z ∈ A.func F (Subtype.val ∘ xs) → z ∈ S) →
        B.part '' (B.func F (f ∘ xs)) ⊆
          A.part '' (A.func F (Subtype.val ∘ xs)) := by
    intro F xs hNonempty _hAll
    rw [nativeOutputPartMask_eq_of_oldDomainMap
      A B S f hMask F xs hNonempty]
  have hNative : IsAmbientRelativeWeakHomomorphism
      A.toStructure S B.toStructure f :=
    ambientRelativeWeakHom_of_splitOutputParts_and_noNewParts
      A B S f hSplitWeak hNoNewParts
  refine ⟨hNative, ?_⟩
  intro x
  have hPart :
      (A.splitMaskHybrid.induce S).rel
        (.inr (.inr (A.part x.1)))
        (fun _ : Fin 1 => x) := rfl
  exact hHybrid (.inr (.inr (A.part x.1)))
    (fun _ : Fin 1 => x) hPart

end AllThoseRamseyClasses.Published
