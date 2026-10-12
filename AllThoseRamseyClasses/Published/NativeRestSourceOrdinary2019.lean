import AllThoseRamseyClasses.Published.NativeOldCopyWeakPiece2019
import AllThoseRamseyClasses.Published.NativeOrdinaryCoordinateRetracts2019
import PartiteConstruction.Ramsey.ClosureAttachmentSubhistory

/-!
# Exact native copy/rest: the REST source map factors into the old picture

The corrected 2019 U-closed Ramsey source may project to a temporary
native Hales--Jewett attachment NONINJECTIVELY. Nevertheless an
ORDINARY source projection carries an exact copy/rest inverse-image
side decomposition (PR #137, under separate audit).

For one exceptional attached copy index i, the REST source set
contains precisely vertices whose projected images are not private
exterior vertices of i. Every such image lies in the TRUE native
subattachment on the complementary line-index set J={j | j≠i}.
The full selected subattachment embeds as an induced substructure
of the original full attachment. Therefore the source projection
RESTRICTED to its exact REST piece factors as an ordinary relational
homomorphism-embedding through that selected subattachment.

If all the retained line indices have a common variable coordinate k,
the ACTUAL selected native power/identity fold is an ordinary
homomorphism-embedding back to the old picture (using the verified
native coordinate reflection from PR #131). Composing produces an
ACTUAL old-picture ordinary HE of the REST source piece.

Neither result needs closure of the REST source or semiclosedness
of the temporary attachment. It does not require global injectivity
or a fictitious map on the complementary copy.

The existential old map is strong enough for the REST half of
maximal-rank two-map completion gluing (PR #130); a compatible A-root
factorization for BOTH sides remains a separate obligation.
No universal higher-rank Picture construction is claimed here.
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

/-- An exact REST piece of an ordinary source projection into an
ACTUAL native attachment factors through the FULL induced selected
subattachment on every copy index j≠i.

No source closedness, map injectivity, or Hales--Jewett parameter
choice is used in this fact. -/
theorem native2019_rest_piece_factors_complement_subfamily
    {U V W I : Type v}
    (Source : RelStructure L U) (Old : RelStructure L V)
    (Support : Set V) (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphismEmbedding
      (attach Old Support Core maps) p)
    (i : I) :
    let J : Set I := {j | j ≠ i}
    let Rest : Set U :=
      {x | ¬ OutsideAt (W := W) (I := I) Support i (p x)}
    ∃ g : Rest → Vertex Support (W := W) (I := J),
      (Source.induce Rest).IsHomomorphismEmbedding
        (attach Old Support Core (fun j : J => maps j.1)) g ∧
      ∀ x : Rest,
        p x.1 = subfamilyEmbedding Old Support Core maps J (g x) := by
  classical
  let J : Set I := {j | j ≠ i}
  let Rest : Set U :=
    {x | ¬ OutsideAt (W := W) (I := I) Support i (p x)}
  let emb := subfamilyEmbedding Old Support Core maps J
  have hRange (x : Rest) :
      ∃ y : Vertex Support (W := W) (I := J),
        p x.1 = emb y := by
    cases hx : p x.1 with
    | inl w =>
        exact ⟨Sum.inl w, rfl⟩
    | inr pair =>
        have hj : pair.1 ∈ J := by
          intro hji
          exact x.2 ⟨pair.2, by simpa [hx, hji]⟩
        exact ⟨Sum.inr (⟨pair.1, hj⟩, pair.2), rfl⟩
  have hpRest :
      (Source.induce Rest).IsHomomorphismEmbedding
        (attach Old Support Core maps)
        (fun x : Rest => p x.1) :=
    hp.comp (inclusion Source Rest).isHomomorphismEmbedding
  exact ordinaryHE_factor_through_embedded_copy_2019
    hpRest emb hRange

variable {P Q V I : Type v} {N : ℕ}

/-- The selected native subattachment on an ARBITRARY set J of
line indices is ordinarily homomorphism-embedded in Old by
coordinate evaluation on its genuine induced power core and
identity on its attached Old copies, provided every line
indexed by J is variable at the selected coordinate.

Unlike the earlier finite-index wrapper, J need not have
decidable membership or a global finite enumeration. -/
theorem native2019_selected_set_coordinate_isOrdinaryHE
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (J : Set I) (k : Fin N)
    (hParam : ∀ i ∈ J, (lines i).symbol k = .parameter) :
    (attach Old.toRelStructure (Old.support alpha)
      (power (Old.restrict alpha) N).toRelStructure
      (fun i : J =>
        (closureLineMaps Old alpha A hRestricted lines) i.1))
      .IsHomomorphismEmbedding Old.toRelStructure
        (fold
          (fun z : NonInduced.Vertex (Old.restrict alpha) N =>
            (z.coord k).1)
          (fun (_ : J) (x : V) => x)) := by
  classical
  let R := Old.restrict alpha
  let Core := (power R N).toRelStructure
  let maps := closureLineMaps Old alpha A hRestricted lines
  let restMaps : J → Embedding (Old.toRelStructure.induce
      (Old.support alpha)) Core :=
    fun i => maps i.1
  let r : NonInduced.Vertex R N → V := fun z => (z.coord k).1
  have hCoord :
      Core.IsHomomorphismEmbedding R.toRelStructure
        (fun z => z.coord k) :=
    native2019_coordinate_isOrdinaryHE_on_restriction
      Old alpha A hRestricted k
  have hInc :
      R.toRelStructure.IsHomomorphismEmbedding Old.toRelStructure
        (fun x => x.1) :=
    (inclusion Old.toRelStructure (Old.support alpha)).isHomomorphismEmbedding
  have hCore : Core.IsHomomorphismEmbedding Old.toRelStructure r :=
    hInc.comp hCoord
  have hInverse : ∀ i : J, ∀ x : Old.support alpha,
      r (restMaps i x) = x.1 := by
    intro i x
    change ((NonInduced.lineMap (lines i.1) x).coord k).1 = x.1
    rw [coordinate_lineMap_parameter
      (lines i.1) k (hParam i.1 i.2) x]
  let pCopy : J → Embedding Old.toRelStructure Old.toRelStructure :=
    fun _ => Embedding.id Old.toRelStructure
  have hFold :
      (attach Old.toRelStructure (Old.support alpha)
        Core restMaps).IsHomomorphismEmbedding Old.toRelStructure
        (fold r (fun i => pCopy i)) :=
    fold_isHomomorphismEmbedding
      (Base := Old.toRelStructure) (S := Old.support alpha)
      (Core := Core) (f := restMaps) (Q := Old.toRelStructure)
      r pCopy hInverse hCore
  change
    (attach Old.toRelStructure (Old.support alpha) Core restMaps)
      .IsHomomorphismEmbedding Old.toRelStructure
      (fold r (fun (_ : J) (x : V) => x))
  exact hFold

/-- If ALL native line indices other than the chosen exceptional
copy i have a common variable coordinate k, the exact REST
source piece (which can be weak and nonclosed) has a CONSTRUCTED
ordinary homomorphism-embedding into Old.

This applies to a selected minimal transverse line family where
removing i restores a parameter coordinate. It makes no assertion
that an arbitrary larger line family still shares that coordinate. -/
theorem native2019_rest_piece_ordinary_old_map
    {U : Type v}
    (Source : RelStructure L U)
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (p : U → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I))
    (hp : Source.IsHomomorphismEmbedding
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p)
    (i : I) (k : Fin N)
    (hOtherParameters : ∀ j : I, j ≠ i →
      (lines j).symbol k = .parameter) :
    let Rest : Set U :=
      {x | ¬ OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) i (p x)}
    ∃ q : Rest → V,
      (Source.induce Rest).IsHomomorphismEmbedding Old.toRelStructure q := by
  classical
  let Rest : Set U :=
    {x | ¬ OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) i (p x)}
  let J : Set I := {j | j ≠ i}
  let maps := closureLineMaps Old alpha A hRestricted lines
  let Core := (power (Old.restrict alpha) N).toRelStructure
  obtain ⟨g, hg, _⟩ :=
    native2019_rest_piece_factors_complement_subfamily
      Source Old.toRelStructure (Old.support alpha) Core
      maps p hp i
  let r : Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := J) → V :=
    fold
      (fun z : NonInduced.Vertex (Old.restrict alpha) N =>
        (z.coord k).1)
      (fun (_ : J) (x : V) => x)
  have hr :
      (attach Old.toRelStructure (Old.support alpha) Core
        (fun j : J => maps j.1)).IsHomomorphismEmbedding
          Old.toRelStructure r :=
    native2019_selected_set_coordinate_isOrdinaryHE
      Old alpha A hRestricted lines J k
        (fun j hj => hOtherParameters j hj)
  exact ⟨r ∘ g, hr.comp hg⟩

end AllThoseRamseyClasses.Published
