import AllThoseRamseyClasses.Published.TrackEOutputPartSplitIrreducibility
import AllThoseRamseyClasses.Published.TrackEFullCopyPartitePullback
import PartiteConstruction.Functional.AmbientRelativeWeakFunctions

/-!
# Track E2: full ambient irreducible tests descend from the split language

The proper native E2 relative weak-HE condition consists of two
independent requirements:
1. IsAmbientRelativeWeakHomomorphism, including the positive clipped
   incidences and equality of complete source fibres;
2. a full target embedding of every ORIGINAL ambient irreducible
   source copy whose vertices lie in the literal weak set S.

The second clause can be transferred from a split-language ambient
relative weak HE, once the original first clause is supplied. The
proof does not assume that arbitrary irreducible native tests were
already part-labelled, that their image under a weak map is injective,
or that any arbitrary split-language amalgam host is canonical.

Every full E ↪ A inherits a genuine part map by E.part := A.part ∘ e.
The pinned splitter lifts e to a full split embedding, and the
universal irreducibility transport in Track E2 makes E.split an
irreducible split test. Split ambient weak-HE then provides a FULL
split embedding into B.split, on the exact f∘e map. Joining the
split target function fibres produces a FULL original embedding of E
into B. No part preservation assumption on the external map f is
needed for the *unlabelled native* HE conclusion.

The remaining sparse-construction and exact local-map obligations are
not proved here. In particular this lemma does not assert that the
current old 2019 whole-mask completion is itself a split HE.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v}

/-- For a genuine canonical split partite System, joining its output
part fibres is not just abstractly isomorphic: it fully embeds BACK
into the original native System on the literal identity vertex map.
No domain reflection is needed outside the image, since the image
is the entire vertex carrier and each fibre is exactly the union. -/
def joinedSplitToOriginalEmbedding
    {V : Type w}
    (B : FunctionalPartite.System L Parts V) :
    Structure.Embedding (joinOutputParts B.splitOutputParts.toStructure)
      B.toStructure where
  toFun := id
  injective := Function.injective_id
  map_rel_iff := fun _ _ => Iff.rfl
  map_func := by
    intro F xs
    ext y
    constructor
    · rintro ⟨z, ⟨q, hz⟩, rfl⟩
      exact hz.1
    · intro hy
      exact ⟨y, ⟨B.part y, ⟨hy, rfl⟩⟩, rfl⟩

/-- The full ambient-irreducible-test clause of native relative weak
HE is inherited from a split-language relative weak HE, provided
the ORIGINAL relative weak homomorphism clause is already certified.

The test E may be an arbitrary full native irreducible structure;
the prescribed source map is the SAME f on the SAME S. The
target full embedding is the joined split-language embedding,
with precisely the original f∘e vertex map. -/
theorem nativeAmbientRelativeWeakHE_of_splitHE_and_nativeWeak
    {V W : Type w}
    (A : FunctionalPartite.System L Parts V)
    (B : FunctionalPartite.System L Parts W)
    (S : Set V) (f : S → W)
    (hSplit : IsAmbientRelativeWeakHE
      A.splitOutputParts.toStructure S
      B.splitOutputParts.toStructure f)
    (hNativeWeak : IsAmbientRelativeWeakHomomorphism
      A.toStructure S B.toStructure f) :
    IsAmbientRelativeWeakHE A.toStructure S B.toStructure f := by
  refine ⟨hNativeWeak, ?_⟩
  intro X E hIrred e he
  let Eparts : FunctionalPartite.System L Parts X :=
    systemOnFullCopy A E e
  have hEpartIrr : Eparts.toStructure.Irreducible := hIrred
  have hSplitIrr : Eparts.splitOutputParts.toStructure.Irreducible :=
    nativeIrreducible_splitOutputParts Eparts hEpartIrr
  let eSplit : FunctionalPartite.Embedding
      Eparts.splitOutputParts A.splitOutputParts :=
    systemOnFullCopy_splitEmbedding A E e
  have heSplit : ∀ x : X, eSplit.toEmbedding x ∈ S := by
    intro x
    exact he x
  obtain ⟨gSplit, hgSplit⟩ :=
    hSplit.2 Eparts.splitOutputParts.toStructure
      hSplitIrr eSplit.toEmbedding heSplit
  let gOriginal : Structure.Embedding E B.toStructure :=
    (joinedSplitToOriginalEmbedding B).comp
      ((joinOutputPartsEmbedding gSplit).comp
        (originalToJoinedSplitEmbedding Eparts))
  refine ⟨gOriginal, ?_⟩
  intro x
  exact hgSplit x

end AllThoseRamseyClasses.Published
