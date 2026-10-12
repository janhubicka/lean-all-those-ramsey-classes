import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosureMaximalWeakRankHereditary
import PartiteConstruction.Iterated.AttachmentProjection

/-!
# Exact 2019 corrected side maps through actual native old-copy ranges

A corrected U-homomorphism-embedding of a CLOSED source T into a
temporarily non-semi-closed native Hales--Jewett little Picture is
NOT generally globally injective. Nevertheless it is an ORDINARY
relational homomorphism-embedding on T: the source's U-closedness
allows protection on ordinary irreducible tests.

If an exact induced piece of T is mapped entirely into the range
of a chosen true attached copy of Old, it factors to Old as an
ordinary homomorphism-embedding. This does not require the whole
temporary attachment to be U-closed or U-semi-closed.

More generally, any ordinary source projection into the actual
attachment admits this factorization on any selected piece whose
image is in one attached old copy. If the original weak source has
MAXIMAL intrinsic U-size, its selected pieces also have maximal
U-size, so the resulting ordinary side map is automatically a
corrected protected U-homomorphism-embedding.

These are the native geometric inputs for completing a maximal
rank-(j+1) weak free cut with two separate ordinary old-picture side
maps. The complementary rest map and COMMON A-boundary compatibility
remain separate; none is invented in this file. The unchanged exact
weak tested source is never replaced by a generated hull.

The general repaired Theorem 2.18 is not proved by this result.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment

universe u v
variable {L : RelLanguage.{u}}

/-- An ordinary homomorphism-embedding whose image lies in one
FULL induced embedded B-copy of C factors as an ordinary
homomorphism-embedding into B. This does not assert global
injectivity of the source map. -/
theorem ordinaryHE_factor_through_embedded_copy_2019
    {U V W : Type v}
    {A : RelStructure L U} {B : RelStructure L V}
    {C : RelStructure L W} {f : U → W}
    (hf : A.IsHomomorphismEmbedding C f)
    (e : Embedding B C)
    (hRange : ∀ x : U, ∃ b : V, f x = e b) :
    ∃ g : U → V, A.IsHomomorphismEmbedding B g ∧
      ∀ x : U, f x = e (g x) := by
  classical
  let g : U → V := fun x => Classical.choose (hRange x)
  have hg (x : U) : f x = e (g x) :=
    Classical.choose_spec (hRange x)
  have hMap : A.IsHomomorphism B g := by
    intro R xs hxs
    have hTarget : C.rel R (e ∘ (g ∘ xs)) := by
      convert hf.1 R xs hxs using 1
      funext j
      exact (hg (xs j)).symm
    exact (e.map_rel_iff R (g ∘ xs)).mp hTarget
  refine ⟨g, ⟨hMap, ?_⟩, hg⟩
  intro S hIrred
  obtain ⟨d, hd⟩ := hf.embeddingOn S hIrred
  have hDS (x : S) : ∃ b : V, d x = e b := by
    obtain ⟨b, hb⟩ := hRange x.1
    exact ⟨b, (hd x).trans hb⟩
  let c : Embedding (A.induce S) B :=
    d.factorThroughRange e hDS
  refine ⟨c, ?_⟩
  intro x
  apply e.injective
  calc
    e (c x) = d x :=
      (Classical.choose_spec (hDS x)).symm
    _ = f x.1 := hd x
    _ = e (g x.1) := hg x.1

/-- Restrict a possibly noninjective ordinary source projection to an
EXACT piece whose image lies inside one genuine old attached copy.
The factor is an ordinary HE into Old; the rest of the attachment
may have conflicting closure tuples. -/
theorem native2019_ordinary_weak_piece_factors_old_copy
    {U V W I : Type v}
    (Source : RelStructure L U) (Old : RelStructure L V)
    (Support : Set V) (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphismEmbedding
      (attach Old Support Core maps) p)
    (S : Set U) (i : I)
    (hInCopy : ∀ x : S,
      ∃ y : V, p x.1 = copyEmbedding Old Support Core maps i y) :
    ∃ g : S → V,
      (Source.induce S).IsHomomorphismEmbedding Old g ∧
      ∀ x : S,
        p x.1 = copyEmbedding Old Support Core maps i (g x) := by
  let f : S → Vertex Support (W := W) (I := I) :=
    fun x => p x.1
  have hPiece :
      (Source.induce S).IsHomomorphismEmbedding
        (attach Old Support Core maps) f :=
    hp.comp (inclusion Source S).isHomomorphismEmbedding
  exact ordinaryHE_factor_through_embedded_copy_2019
    hPiece (copyEmbedding Old Support Core maps i) hInCopy

/-- A corrected protected projection from a U-CLOSED source into a
nonclosed native Picture gives an ORDINARY HE on any exact piece
entirely in an attached old copy. No global injectivity is used. -/
theorem native2019_closed_source_piece_factors_old_copy
    {rules : ClosureDescription L}
    {U V W I : Type v}
    (Source : RelStructure L U) (hClosed : IsUClosed rules Source)
    (Old : RelStructure L V) (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : IsInducedClosedUHomomorphismEmbedding rules
      Source (attach Old Support Core maps) p)
    (S : Set U) (i : I)
    (hInCopy : ∀ x : S,
      ∃ y : V, p x.1 = copyEmbedding Old Support Core maps i y) :
    ∃ g : S → V,
      (Source.induce S).IsHomomorphismEmbedding Old g ∧
      ∀ x : S,
        p x.1 = copyEmbedding Old Support Core maps i (g x) := by
  have hOrd :
      Source.IsHomomorphismEmbedding
        (attach Old Support Core maps) p :=
    IsClosedUHomomorphismEmbedding.toHomomorphismEmbedding_of_closed
      (IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hp)
      hClosed
  exact native2019_ordinary_weak_piece_factors_old_copy
    Source Old Support Core maps p hOrd S i hInCopy

/-- For a maximal-U-rank WEAK source, each exact induced piece has
maximal U-size and hence its ordinary old-copy map ALREADY protects
closed U-irreducible tests. No intrinsic closedness is required. -/
theorem native2019_maximal_weak_piece_protected_old_copy
    {rules : ClosureDescription L}
    {U V W I : Type v}
    [Fintype U]
    (Source : RelStructure L U)
    (hMax : USize rules Source = Fintype.card U)
    (Old : RelStructure L V) (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphismEmbedding
      (attach Old Support Core maps) p)
    (S : Set U) [Fintype S] (i : I)
    (hInCopy : ∀ x : S,
      ∃ y : V, p x.1 = copyEmbedding Old Support Core maps i y) :
    ∃ g : S → V,
      IsInducedClosedUHomomorphismEmbedding rules
        (Source.induce S) Old g ∧
      ∀ x : S,
        p x.1 = copyEmbedding Old Support Core maps i (g x) := by
  obtain ⟨g, hg, hFactor⟩ :=
    native2019_ordinary_weak_piece_factors_old_copy
      Source Old Support Core maps p hp S i hInCopy
  have hMaxPiece :
      USize rules (Source.induce S) = Fintype.card S :=
    induced_USize_eq_card_of_max_USize rules Source hMax S
  exact ⟨g, IsClosedUHomomorphismEmbedding.toInducedClosed
    (hg.toClosedMap_of_max_USize hMaxPiece), hFactor⟩

end AllThoseRamseyClasses.Published
