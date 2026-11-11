import PartiteConstruction.Functional.OutputPartSingletonization
import PartiteConstruction.Structure.FreeAmalgam

/-!
# Track E2: output-part singleton splitting preserves native irreducibility

A native function application with several output parts is encoded by
separate (F,q) singleton-valued fibres. To protect full ambient
irreducible tests by a split-language weak HE, one needs to know that
native irreducible tests remain irreducible after splitting.

This is NOT an assumption about the finite test's Gaifman graph:
the image of a full functional embedding is function-closed, which
must be respected in every genuine free amalgam. Instead we show the
universal irreducibility assertion directly, for free amalgams even
of NONCANONICAL split-language structures.

For an arbitrary split-language Structure X, join all output-part
fibres into one original F-fibre. This operation sends full split
embeddings to full original embeddings and sends genuine split free
amalgam diagrams to genuine original free amalgam diagrams. The join
of a canonical split native System receives a full identity-vertex
embedding from the original native System. A hypothetical split free
amalgam crossing an irreducible original copy would therefore
contradict native irreducibility.

No closedness hull, extra vertices, partite assumption on an arbitrary
free-amalgam host, or source weak homomorphism is introduced.
The converse direction and the final full ambient weak HE remain
separate from this statement.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey

universe u v w z
variable {L : Language.{u}} {Parts : Type v}

/-- Interpret an arbitrary output-part-indexed functional structure
back in the original language, by taking the union of its fibres.
No part map or coherence requirement on the expanded structure. -/
def joinOutputParts {V : Type w}
    (X : Structure (L.outputPartIndexed Parts) V) : Structure L V where
  rel R xs := X.rel (ULift.up R) xs
  func F xs := {y | ∃ q : Parts, y ∈ X.func (ULift.up F, q) xs}

/-- A full embedding of arbitrary split-language structures is a full
embedding of their unsplit fibre-union interpretations, on the same
vertex function. -/
def joinOutputPartsEmbedding
    {V : Type w} {W : Type z}
    {X : Structure (L.outputPartIndexed Parts) V}
    {Y : Structure (L.outputPartIndexed Parts) W}
    (e : Structure.Embedding X Y) :
    Structure.Embedding (joinOutputParts X) (joinOutputParts Y) where
  toFun := e
  injective := e.injective
  map_rel_iff R xs := e.map_rel_iff (ULift.up R) xs
  map_func := by
    intro F xs
    ext y
    constructor
    · rintro ⟨a, ⟨q, ha⟩, rfl⟩
      refine ⟨q, ?_⟩
      have hInImage :
          e a ∈ Structure.imageSet e
            (X.func (ULift.up F, q) xs) := ⟨a, ha, rfl⟩
      exact (e.map_func (ULift.up F, q) xs) ▸ hInImage
    · rintro ⟨q, hq⟩
      have hInImage :
          y ∈ Structure.imageSet e
            (X.func (ULift.up F, q) xs) :=
        (e.map_func (ULift.up F, q) xs).symm ▸ hq
      obtain ⟨a, ha, rfl⟩ := hInImage
      exact ⟨a, ⟨q, ha⟩, rfl⟩

/-- The original native System fully embeds, with the identity vertex
map, in the union of the singleton fibres of its canonical split.
The output sets are literally reconstructed by choosing q=part(y). -/
def originalToJoinedSplitEmbedding
    {V : Type w}
    (A : StructuralRamsey.FunctionalPartite.System L Parts V) :
    Structure.Embedding A.toStructure (joinOutputParts A.splitOutputParts.toStructure) where
  toFun := id
  injective := Function.injective_id
  map_rel_iff := fun _ _ => Iff.rfl
  map_func := by
    intro F xs
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨A.part a, ha, rfl⟩
    · rintro ⟨q, hq⟩
      exact ⟨y, hq.1, rfl⟩

/-- Joining the output-part fibres of an ARBITRARY split free amalgam
produces an original-language free amalgam. The four vertex maps
and the overlap/covering diagrams are literally unchanged. -/
theorem joinOutputParts_freeAmalgam
    {H E F C : Type w}
    {Dsrc : Structure (L.outputPartIndexed Parts) H}
    {Esrc : Structure (L.outputPartIndexed Parts) E}
    {Fsrc : Structure (L.outputPartIndexed Parts) F}
    {Csrc : Structure (L.outputPartIndexed Parts) C}
    {sE : Structure.Embedding Dsrc Esrc}
    {sF : Structure.Embedding Dsrc Fsrc}
    {iE : Structure.Embedding Esrc Csrc}
    {iF : Structure.Embedding Fsrc Csrc}
    (hFree : Structure.IsFreeAmalgam sE sF iE iF) :
    Structure.IsFreeAmalgam
      (joinOutputPartsEmbedding sE) (joinOutputPartsEmbedding sF)
      (joinOutputPartsEmbedding iE) (joinOutputPartsEmbedding iF) := by
  constructor
  · exact hFree.covers
  · exact hFree.overlap
  · intro R xs
    exact hFree.rel_iff (ULift.up R) xs
  · intro F0 xs y
    constructor
    · rintro ⟨q, hq⟩
      rcases (hFree.func_iff (ULift.up F0, q) xs y).mp hq with hE | hF
      · rcases hE with ⟨args, out, hout, hargs, hy⟩
        exact Or.inl ⟨args, out, ⟨q, hout⟩, hargs, hy⟩
      · rcases hF with ⟨args, out, hout, hargs, hy⟩
        exact Or.inr ⟨args, out, ⟨q, hout⟩, hargs, hy⟩
    · intro h
      rcases h with hE | hF
      · rcases hE with ⟨args, out, ⟨q, hout⟩, hargs, hy⟩
        exact ⟨q, (hFree.func_iff (ULift.up F0, q) xs y).mpr
          (Or.inl ⟨args, out, hout, hargs, hy⟩)⟩
      · rcases hF with ⟨args, out, ⟨q, hout⟩, hargs, hy⟩
        exact ⟨q, (hFree.func_iff (ULift.up F0, q) xs y).mpr
          (Or.inr ⟨args, out, hout, hargs, hy⟩)⟩

/-- ORIGINAL native irreducibility implies irreducibility of the
CANONICAL split-language presentation, against arbitrary expanded
split free-amalgam hosts (not only canonical/partite ones).

This is the structural irreducible-copy half required to apply a
split-language `IsAmbientRelativeWeakHE` to an original irreducible
test. It does NOT independently produce a split weak HE certificate. -/
theorem nativeIrreducible_splitOutputParts
    {V : Type w}
    (A : StructuralRamsey.FunctionalPartite.System L Parts V)
    (hA : A.toStructure.Irreducible) :
    A.splitOutputParts.toStructure.Irreducible := by
  intro H E F C Dsrc Esrc Fsrc Csrc sE sF iE iF hFree e
  have hJoined : Structure.IsFreeAmalgam
      (joinOutputPartsEmbedding sE) (joinOutputPartsEmbedding sF)
      (joinOutputPartsEmbedding iE) (joinOutputPartsEmbedding iF) :=
    joinOutputParts_freeAmalgam hFree
  let eOriginal : Structure.Embedding A.toStructure (joinOutputParts Csrc) :=
    (joinOutputPartsEmbedding e).comp (originalToJoinedSplitEmbedding A)
  rcases hA hJoined eOriginal with hLeft | hRight
  · exact Or.inl (fun x => hLeft x)
  · exact Or.inr (fun x => hRight x)

end AllThoseRamseyClasses.Published
