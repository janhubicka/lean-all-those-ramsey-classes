import AllThoseRamseyClasses.Lifts.NativeNonemptyPartialBridge

/-!
# Track E: full faithfulness in the reverse direction of native partial encoding

The faithful native encoding sends each original nonempty
set-valued output fibre to some of that exact fibre and
each empty/undefined fibre to none.

PR #846 established that every FULL original functional
embedding lifts to a full embedding in this independent-domain
Option(Set) representation.

Conversely, if the faithful partial representations of two
native structures admit a FULL partial embedding, the same
vertex map is already a FULL original native embedding.
This is not merely a positive graph homomorphism: target
function-domain reflection, complete output-fibre equality,
injectivity, and reflection of every relation predicate
are all inherited from the full partial embedding.

The two directions provide a genuinely faithful FULL
embedding interface for specializing the certified two-pass
2019 whole-mask/profiling construction. They do NOT say that
arbitrary relational profile targets are decodable, or that
all positive weak partial projections become full embeddings.
The final class-level Ramsey transfer remains open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}}

/-- A full partial-set-functional embedding between the
canonical faithful encodings of native structures reflects
to a FULL native functional embedding.

The proof explicitly distinguishes both possible source
and target domain states; there is no conflation of
defined-empty with undefined in the richer category,
because defined-empty never occurs in an encoded native
structure. -/
noncomputable def nativeFullEmbedding_of_partialEncodingEmbedding
    {VA : Type v} {VB : Type w}
    {A : Structure L VA} {B : Structure L VB}
    (e : PartialSetStructure.Embedding
      (nativeToNonemptyPartial A)
      (nativeToNonemptyPartial B)) :
    Structure.Embedding A B where
  toFun := e.toFun
  injective := e.injective
  map_rel_iff := by
    intro R xs
    exact e.map_rel_iff R xs
  map_func := by
    intro F xs
    classical
    have h := e.map_func F xs
    by_cases hA : (A.func F xs).Nonempty
    · by_cases hB : (B.func F (e.toFun ∘ xs)).Nonempty
      · simpa [nativeToNonemptyPartial, hA, hB] using h
      · simp [nativeToNonemptyPartial, hA, hB] at h
    · by_cases hB : (B.func F (e.toFun ∘ xs)).Nonempty
      · simp [nativeToNonemptyPartial, hA, hB] at h
      · have hAEmpty : A.func F xs = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hA
        have hBEmpty : B.func F (e.toFun ∘ xs) = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hB
        simp [hAEmpty, hBEmpty, Structure.imageSet]

/-- The recovered full native embedding has EXACTLY the
original underlying vertex map of its partial encoding
embedding; no generated closure or new representation
vertices are inserted. -/
@[simp] theorem nativeFullEmbedding_of_partialEncodingEmbedding_apply
    {VA : Type v} {VB : Type w}
    {A : Structure L VA} {B : Structure L VB}
    (e : PartialSetStructure.Embedding
      (nativeToNonemptyPartial A)
      (nativeToNonemptyPartial B)) (x : VA) :
    nativeFullEmbedding_of_partialEncodingEmbedding e x =
      e.toFun x := rfl

end AllThoseRamseyClasses.Lifts
