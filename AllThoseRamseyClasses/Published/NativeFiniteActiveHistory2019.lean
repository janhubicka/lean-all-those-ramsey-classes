import AllThoseRamseyClasses.Published.NativeOldCopyWeakPiece2019
import PartiteConstruction.Ramsey.ClosureAttachmentSubhistory

/-!
# A FINITE exact weak test sees a FINITE native HJ copy subhistory

The actual native Hales--Jewett attachment may use an arbitrary index
type I and an enormous family of lines. The exact weak test has only
finitely many vertices. Each vertex belongs either to the common
power core or to the private exterior of ONE attached old copy.

Define the finite active set by taking the union, for each source
vertex, of either the empty index set (core) or its singleton exterior
copy index. Prove membership iff some ACTUAL tested vertex lies in
that private exterior; no unused line can enter this set.

The original exact source map (which may identify unrelated vertices)
then factors as an ORDINARY relational homomorphism-embedding into the
true induced subattachment on this finite active set. The factorization
is vertex-exact and uses neither U-closedness nor semiclosedness.

This is a useful interface between the arbitrary-index native attachment
and the finite minimal-no-common-coordinate HJ history theorem. Further
shrinking the full ACTIVE subhistory to a smaller obstructing family
while retaining every source vertex is not claimed. Neither common
A-boundary nor universal higher-rank Picture promotion is proved.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment

universe u v
variable {L : RelLanguage.{u}}

/-- The finite set of copy indices genuinely used by an exact finite
source projection to private outside vertices of a simultaneous
attachment. A core vertex contributes no index. -/
noncomputable def native2019_exact_active_index_finset
    {U V W I : Type v}
    [Fintype U]
    (Support : Set V)
    (p : U → Vertex Support (W := W) (I := I)) : Finset I := by
  classical
  exact (Finset.univ : Finset U).biUnion (fun x =>
    match p x with
    | Sum.inl _ => ∅
    | Sum.inr pair => {pair.1})

/-- Membership is EXACTLY witnessed by some original weak source
vertex in the corresponding private exterior. -/
theorem native2019_mem_exact_active_index_iff
    {U V W I : Type v}
    [Fintype U]
    (Support : Set V)
    (p : U → Vertex Support (W := W) (I := I))
    (i : I) :
    i ∈ native2019_exact_active_index_finset Support p ↔
      ∃ x : U,
        OutsideAt (W := W) (I := I) Support i (p x) := by
  classical
  unfold native2019_exact_active_index_finset
  constructor
  · intro h
    obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp h
    cases hp : p x with
    | inl w =>
        simp [hp] at hx
    | inr pair =>
        rcases pair with ⟨j, b⟩
        have heq : i = j := by simpa [hp] using hx
        subst i
        exact ⟨x, b, hp⟩
  · rintro ⟨x, b, hp⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨x, Finset.mem_univ x, ?_⟩
    simp [hp]

/-- For a finite original exact weak source the ACTUAL potentially
noninjective ordinary projection factors through a native subattachment
indexed by a concrete FINSET of ALL its private-active copy indices.

No test vertex is closed, discarded or assigned an artificial copy. -/
theorem native2019_finite_exact_source_factors_active_subhistory
    {U V W I : Type v}
    [Fintype U]
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphismEmbedding
      (attach Old Support Core maps) p) :
    let T := native2019_exact_active_index_finset Support p
    ∃ q : U → Vertex Support (W := W) (I := (↑T : Set I)),
      Source.IsHomomorphismEmbedding
        (attach Old Support Core
          (fun i : (↑T : Set I) => maps i.1)) q ∧
      ∀ x : U,
        p x = subfamilyEmbedding Old Support Core maps
          (↑T : Set I) (q x) := by
  classical
  let T := native2019_exact_active_index_finset Support p
  let J : Set I := (↑T : Set I)
  let emb := subfamilyEmbedding Old Support Core maps J
  have hRange (x : U) :
      ∃ y : Vertex Support (W := W) (I := J),
        p x = emb y := by
    cases hx : p x with
    | inl w =>
        exact ⟨Sum.inl w, rfl⟩
    | inr pair =>
        have hi : pair.1 ∈ J := by
          apply (native2019_mem_exact_active_index_iff Support p pair.1).mpr
          exact ⟨x, pair.2, hx⟩
        exact ⟨Sum.inr (⟨pair.1, hi⟩, pair.2), rfl⟩
  exact ordinaryHE_factor_through_embedded_copy_2019 hp emb hRange

end AllThoseRamseyClasses.Published
