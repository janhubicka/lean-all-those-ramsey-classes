import AllThoseRamseyClasses.Published.NativeRestSourceOrdinary2019
import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization

/-!
# Closed-Picture protected projections give ORDINARY maps of exact weak REST pieces

The native complementary-index REST theorem takes an ORDINARY source
homomorphism-embedding. The actual 2019 protected Picture map is formulated
as a corrected U-homomorphism-embedding into a possibly NONCLOSED temporary
native attachment. One must not silently strengthen an arbitrary weak
source map to an ordinary HE.

Here the source of the ACTUAL full-Picture projection is U-CLOSED. This
suffices to upgrade the protected map to an ordinary HE, which can then
be restricted to an exact, possibly nonclosed weak induced test S. Applying
the native complementary-rest theorem gives an ORDINARY old-Picture HE
on the literal weak REST of S whenever the OTHER attachment indices have
one common parameter coordinate.

This is a genuine bridge between the corrected published Lemma 2.30
hypotheses and the native REST-side constructor of PR #138; it uses
neither artificial closure of S nor semiclosedness of the attachment.

The exceptional copy-side map, proper source cut, selected-history
localization and common A-root on BOTH sides remain separate obligations.
No general strict rank increment or repaired Theorem 2.18 is claimed.
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
variable {P Q V I : Type v} {N : ℕ}

/-- The FULL source is closed and carries the corrected protected map to
the ACTUAL possibly nonclosed Hales--Jewett attachment. On ANY exact
induced WEAK test S, the literal REST piece has an ordinary HE to Old
provided every line other than the chosen exception i is parameter at k.

The induced source is not enlarged to its ambient closure. -/
theorem native2019_closed_picture_exact_weak_rest_old_map
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
    (S : Set U)
    (i : I) (k : Fin N)
    (hOtherParameters : ∀ j : I, j ≠ i →
      (lines j).symbol k = .parameter) :
    let Rest : Set S :=
      {x | ¬ OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) i (p x.1)}
    ∃ q : Rest → V,
      ((Source.induce S).induce Rest).IsHomomorphismEmbedding
        Old.toRelStructure q := by
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
  let pS : S → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I) :=
    fun x => p x.1
  have hpS :
      (Source.induce S).IsHomomorphismEmbedding
        (attach Old.toRelStructure (Old.support alpha)
          (power (Old.restrict alpha) N).toRelStructure
          (closureLineMaps Old alpha A hRestricted lines)) pS :=
    hpOrd.comp (inclusion Source S).isHomomorphismEmbedding
  exact native2019_rest_piece_ordinary_old_map
    (Source.induce S) Old alpha A hRestricted lines pS
    hpS i k hOtherParameters

end AllThoseRamseyClasses.Published
