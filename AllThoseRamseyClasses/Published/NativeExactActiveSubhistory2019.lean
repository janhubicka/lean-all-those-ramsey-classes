import AllThoseRamseyClasses.Published.NativeClosedPictureWeakRest2019
import PartiteConstruction.Ramsey.ClosureAttachmentSubhistory

/-!
# Exact 2019 weak test factors through ALL and ONLY its active native copy indices

The abstract full native Hales--Jewett history may have many lines that a
particular weak test never meets. One cannot apply the minimal transverse
subfamily argument to the entire attachment and silently ignore other
private-active lines.

This file performs the first *exact* geometric localization.
For an ordinary (possibly globally noninjective) map of the ORIGINAL weak
source into a true simultaneous attachment, take the set J consisting
precisely of indices with an actual source vertex in their PRIVATE
exterior. Every projected vertex then lies in the full induced
subattachment keeping the entire power core and just copies J.
The existing source map factors through that induced subattachment
as an ORDINARY homomorphism-embedding, with equality of its composite
to the original native source map at EVERY original vertex.

The second theorem applies this to any exact weak induced test inside
a closed full Picture whose projection is the corrected protected
2019 map. No weak source is replaced by its closure hull. No closure
or semiclosedness of the intermediate attachment is required.

This eliminates *inactive* omitted indices from the history. It does
NOT yet justify deleting further active lines to leave a minimal
transverse family: those remaining omitted ACTIVE indices remain
a genuine obstacle. Nor does it supply the common A-root.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment
open StructuralRamsey.Partite
open StructuralRamsey.Partite.Induced
open StructuralRamsey.HalesJewett

universe u v
variable {L : RelLanguage.{u}}

/-- The original exact weak source admits an ORDINARY factorization
through the actual induced subattachment indexed by its private-active
indices J. The map may be globally noninjective. -/
theorem native2019_exact_source_factors_all_active_subhistory
    {U V W I : Type v}
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphismEmbedding
      (attach Old Support Core maps) p) :
    let J : Set I :=
      {i | ∃ x : U,
        OutsideAt (W := W) (I := I) Support i (p x)}
    ∃ q : U → Vertex Support (W := W) (I := J),
      Source.IsHomomorphismEmbedding
        (attach Old Support Core (fun i : J => maps i.1)) q ∧
      ∀ x : U,
        p x = subfamilyEmbedding Old Support Core maps J (q x) := by
  classical
  let J : Set I :=
    {i | ∃ x : U,
      OutsideAt (W := W) (I := I) Support i (p x)}
  let emb := subfamilyEmbedding Old Support Core maps J
  have hRange (x : U) :
      ∃ y : Vertex Support (W := W) (I := J), p x = emb y := by
    cases hx : p x with
    | inl w =>
        exact ⟨Sum.inl w, rfl⟩
    | inr pair =>
        have hi : pair.1 ∈ J := by
          exact ⟨x, pair.2, hx⟩
        exact ⟨Sum.inr (⟨pair.1, hi⟩, pair.2), rfl⟩
  exact ordinaryHE_factor_through_embedded_copy_2019 hp emb hRange

variable {P Q V I : Type v} {N : ℕ}

/-- Corrected protected projection of the CLOSED full Picture restricts to
an ordinary map on the original exact possibly nonclosed weak induced S.
It factors through only those genuine native HJ line indices which occur
as PRIVATE exteriors of actual source vertices in S. -/
theorem native2019_closed_picture_weak_test_factors_active_subhistory
    {rules : ClosureDescription L}
    {U : Type v}
    (Source : RelStructure L U)
    (hClosed : IsUClosed rules Source)
    (Old : System L P V)
    (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (p : U → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I))
    (hp : IsInducedClosedUHomomorphismEmbedding rules Source
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p)
    (S : Set U) :
    let J : Set I :=
      {i | ∃ x : S,
        OutsideAt
          (W := NonInduced.Vertex (Old.restrict alpha) N)
          (I := I) (Old.support alpha) i (p x.1)}
    ∃ q : S → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := J),
      (Source.induce S).IsHomomorphismEmbedding
        (attach Old.toRelStructure (Old.support alpha)
          (power (Old.restrict alpha) N).toRelStructure
          (fun i : J =>
            (closureLineMaps Old alpha A hRestricted lines) i.1)) q ∧
      ∀ x : S,
        p x.1 =
          subfamilyEmbedding Old.toRelStructure
            (Old.support alpha)
            (power (Old.restrict alpha) N).toRelStructure
            (closureLineMaps Old alpha A hRestricted lines) J (q x) := by
  have hpAbstract :
      IsClosedUHomomorphismEmbedding rules Source
        (attach Old.toRelStructure (Old.support alpha)
          (power (Old.restrict alpha) N).toRelStructure
          (closureLineMaps Old alpha A hRestricted lines)) p :=
    IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hp
  have hpOrd :
      Source.IsHomomorphismEmbedding
        (attach Old.toRelStructure (Old.support alpha)
          (power (Old.restrict alpha) N).toRelStructure
          (closureLineMaps Old alpha A hRestricted lines)) p :=
    IsClosedUHomomorphismEmbedding.toHomomorphismEmbedding_of_closed
      hpAbstract hClosed
  have hpS :
      (Source.induce S).IsHomomorphismEmbedding
        (attach Old.toRelStructure (Old.support alpha)
          (power (Old.restrict alpha) N).toRelStructure
          (closureLineMaps Old alpha A hRestricted lines))
        (fun x : S => p x.1) :=
    hpOrd.comp (inclusion Source S).isHomomorphismEmbedding
  exact native2019_exact_source_factors_all_active_subhistory
    (Source.induce S) Old.toRelStructure (Old.support alpha)
    (power (Old.restrict alpha) N).toRelStructure
    (closureLineMaps Old alpha A hRestricted lines)
    (fun x : S => p x.1) hpS

end AllThoseRamseyClasses.Published
