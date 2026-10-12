import AllThoseRamseyClasses.Published.NativePositivePullbackFreeCut2019
import AllThoseRamseyClasses.Published.NativeClosedPictureWeakRest2019

/-!
# Exact native 2019 weak copy/rest: the free split has TWO ordinary old maps

Combine the CI-green native source free-cut pullback (PR #137), the native
complementary-REST coordinate retraction (PR #138), and its bridge from
the corrected protected map of the closed full Picture (PR #140).

For ANY exact induced weak test S of the closed full Picture, if all OTHER
copy indices j != i have a common parameter coordinate k, then:

* the inverse-image of the chosen actual Old copy carries an ORDINARY
  source-side HE into Old;
* the inverse-image of its complementary REST carries another ORDINARY
  source-side HE into Old;
* the two exact source-side sets form a genuine relational free amalgam
  over their literal intersection.

The two old-Picture maps may disagree on that intersection and generally
do not factor through a common A-embedding. No assumption of temporary
U-semi-closedness or injectivity of the global corrected projection is made.

Thus the remaining genuine proof obligations are the native exceptional
line/history dichotomy, properness of the chosen source cut, localization
to an actual compatible line subfamily, and the vertex-level A-boundary.
No repaired unrestricted Theorem 2.18 is claimed here.
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

/-- For the two EXACT induced weak source pieces of the native copy/rest cut,
produce ordinary old-Picture side maps and prove their relational freeness.
The only coordinate hypothesis is that all *other* line indices share k.
Neither side is replaced with its U-closure. -/
theorem native2019_closed_picture_exact_weak_two_old_maps_and_free
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
    (S : Set U) (i : I) (k : Fin N)
    (hParam : ∀ j : I, j ≠ i →
      (lines j).symbol k = .parameter) :
    let Support := Old.support alpha
    let Core := (power (Old.restrict alpha) N).toRelStructure
    let maps := closureLineMaps Old alpha A hRestricted lines
    let Copy : Set S :=
      {x | InCopy Old.toRelStructure Support Core maps i (p x.1)}
    let Rest : Set S :=
      {x | ¬ OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) Support i (p x.1)}
    ∃ (pLeft : Copy → V) (pRight : Rest → V),
      ((Source.induce S).induce Copy).IsHomomorphismEmbedding
        Old.toRelStructure pLeft ∧
      ((Source.induce S).induce Rest).IsHomomorphismEmbedding
        Old.toRelStructure pRight ∧
      IsFreeAmalgam
        (exactFreeCoverRootToLeft (Source.induce S) Copy Rest)
        (exactFreeCoverRootToRight (Source.induce S) Copy Rest)
        (inclusion (Source.induce S) Copy)
        (inclusion (Source.induce S) Rest) := by
  classical
  let Support := Old.support alpha
  let Core := (power (Old.restrict alpha) N).toRelStructure
  let maps := closureLineMaps Old alpha A hRestricted lines
  let pS : S → Vertex Support
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I) :=
    fun x => p x.1
  let Copy : Set S :=
    {x | InCopy Old.toRelStructure Support Core maps i (p x.1)}
  let Rest : Set S :=
    {x | ¬ OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) Support i (p x.1)}
  have hAbstract :
      IsClosedUHomomorphismEmbedding rules Source
        (attach Old.toRelStructure Support Core maps) p :=
    IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hp
  have hOrd :
      Source.IsHomomorphismEmbedding
        (attach Old.toRelStructure Support Core maps) p :=
    IsClosedUHomomorphismEmbedding.toHomomorphismEmbedding_of_closed
      hAbstract hClosed
  have hS :
      (Source.induce S).IsHomomorphismEmbedding
        (attach Old.toRelStructure Support Core maps) pS :=
    hOrd.comp (inclusion Source S).isHomomorphismEmbedding
  have hCopyRange : ∀ x : Copy,
      ∃ y : V,
        pS x.1 =
          copyEmbedding Old.toRelStructure Support Core maps i y := by
    intro x
    exact x.2
  obtain ⟨pLeft, hLeft, _⟩ :=
    native2019_ordinary_weak_piece_factors_old_copy
      (Source.induce S) Old.toRelStructure Support Core
      maps pS hS Copy i hCopyRange
  obtain ⟨pRight, hRight⟩ :=
    native2019_closed_picture_exact_weak_rest_old_map
      Source hClosed Old alpha A hRestricted lines
      p hp S i k hParam
  have hFree :
      IsFreeAmalgam
        (exactFreeCoverRootToLeft (Source.induce S) Copy Rest)
        (exactFreeCoverRootToRight (Source.induce S) Copy Rest)
        (inclusion (Source.induce S) Copy)
        (inclusion (Source.induce S) Rest) :=
    native2019_positive_source_copy_rest_free
      (Source.induce S) Old.toRelStructure Support Core
      maps pS hS.1 i
  exact ⟨pLeft, pRight, hLeft, hRight, hFree⟩

end AllThoseRamseyClasses.Published
