import AllThoseRamseyClasses.Published.MinimalNoncommonHJ2019
import PartiteConstruction.Ramsey.ClosurePictureCoordinate
import PartiteConstruction.Ramsey.ClosurePictureRetraction

/-!
# Actual native retractions for the REST of every minimal bad HJ line family

A family of selected genuine Hales--Jewett lines may have NO common
variable coordinate, even when every pair has one. The verified
minimum-bad-family lemma selects a minimal family T with no
common coordinate, and gives for each exceptional line i in T a
coordinate k_i which is variable on ALL remaining lines T.erase i.

In the ACTUAL closed-support native Picture attachment, the
selected attachment on those remaining lines is U-closed, even if
the entire source family contains other conflicting lines.
Coordinate evaluation at k_i on the native power core, plus the
identity on every remaining attached old copy, is a genuine
protected U-homomorphism-embedding back into the old U-closed picture.

The first theorem constructs this PROTECTED MAP for any selected
coordinate-compatible subfamily; the second combines it with the
minimal-bad finite selection, so that EVERY one-line deletion of
a minimal bad family carries a concrete old-picture retraction.

No K-completion oracle or artificial map is supplied. This is
genuine Hales--Jewett attachment geometry. It does NOT yet
construct a compatible protected map of the EXCEPTIONAL side, a
proper free split of every original rank-(j+1) closed source, or
the common closed K-boundary needed to glue two completions.
The general j-to-j+1 Ramsey construction remains OPEN.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Partite
open StructuralRamsey.Partite.Induced
open StructuralRamsey.HalesJewett

universe u v
variable {L : RelLanguage.{u}}
variable {P Q V I : Type v} {N : ℕ}

/-- The EXACT native subattachment with just the selected J
line indices; all core vertices remain, and unselected exterior
old-copy vertices are omitted. -/
noncomputable def selectedNativeHJAttachment2019
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (J : Finset I) :
    RelStructure L
      (RelStructure.Attachment.Vertex (Old.support alpha)
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := (↑J : Set I))) :=
  RelStructure.Attachment.attach Old.toRelStructure (Old.support alpha)
    (power (Old.restrict alpha) N).toRelStructure
    (fun i : (↑J : Set I) =>
      (closureLineMaps Old alpha A hRestricted lines) i.1)

/-- Evaluate the real native power core at coordinate k, and
send each private attached-copy vertex to its original old
vertex. This is only a FUNCTION until its line-parameter
compatibility and protection have been proved below. -/
def selectedNativeHJCoordinateMap2019
    (Old : System L P V) (alpha : Q ↪ P)
    (J : Finset I) (k : Fin N) :
    RelStructure.Attachment.Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := (↑J : Set I)) → V :=
  RelStructure.Attachment.fold
    (fun z : NonInduced.Vertex (Old.restrict alpha) N => (z.coord k).1)
    (fun (_ : (↑J : Set I)) (x : V) => x)

/-- An actual selected line family with a common variable coordinate
has a PROTECTED coordinate evaluation/identity retraction into Old.
The whole original attachment is U-closed and its support closed;
closedness of the selected rest follows by the native subhistory lemma.

The theorem does not require J to contain all original lines. -/
theorem selectedNativeHJCoordinateMap2019_protected
    {rules : ClosureDescription L}
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (hOld : IsUClosed rules Old.toRelStructure)
    (hSupport : IsUSubstructure rules Old.toRelStructure (Old.support alpha))
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power (Old.restrict alpha) N).toRelStructure A
      (power (Old.restrict alpha) N).part)
    (hWhole : IsUClosed rules
      (RelStructure.Attachment.attach Old.toRelStructure
        (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)))
    (J : Finset I) (k : Fin N)
    (hParameters : ∀ i ∈ J, (lines i).symbol k = .parameter) :
    IsClosedUHomomorphismEmbedding rules
      (selectedNativeHJAttachment2019 Old alpha A hRestricted lines J)
      Old.toRelStructure
      (selectedNativeHJCoordinateMap2019 Old alpha J k) := by
  classical
  let R := Old.restrict alpha
  let Core := (power R N).toRelStructure
  let allMaps := closureLineMaps Old alpha A hRestricted lines
  let Jset : Set I := (↑J : Set I)
  let mapsRest : Jset →
      RelStructure.Embedding
        (Old.toRelStructure.induce (Old.support alpha)) Core :=
    fun i => allMaps i.1
  have hRestClosed :
      IsUClosed rules
        (RelStructure.Attachment.attach Old.toRelStructure
          (Old.support alpha) Core mapsRest) :=
    RelStructure.Attachment.subfamily_isUClosed
      Old.toRelStructure (Old.support alpha) Core allMaps
      hSupport hWhole Jset
  let r : NonInduced.Vertex R N → V := fun z => (z.coord k).1
  have hr : IsClosedUHomomorphismEmbedding rules
      Core Old.toRelStructure r :=
    ((RelStructure.inclusion Old.toRelStructure
      (Old.support alpha)).isClosedUHomomorphismEmbedding rules).comp
      (coordinate_closedMap R k hRestricted.1 hPower)
  have hInverse : ∀ i : Jset, ∀ x : Old.support alpha,
      r (mapsRest i x) = x.1 := by
    intro i x
    change ((NonInduced.lineMap (lines i.1) x).coord k).1 = x.1
    rw [coordinate_lineMap_parameter
      (lines i.1) k (hParameters i.1 i.2) x]
  have hCopy : ∀ i : Jset,
      IsClosedUHomomorphismEmbedding rules
        Old.toRelStructure Old.toRelStructure (fun x : V => x) :=
    fun _ => (RelStructure.Embedding.id Old.toRelStructure).isClosedUHomomorphismEmbedding rules
  change IsClosedUHomomorphismEmbedding rules
    (RelStructure.Attachment.attach Old.toRelStructure
      (Old.support alpha) Core mapsRest) Old.toRelStructure
    (RelStructure.Attachment.fold r
      (fun (_ : Jset) (x : V) => x))
  exact RelStructure.Attachment.fold_isClosedUHomomorphismEmbedding
    Old.toRelStructure (Old.support alpha) Core mapsRest
    hOld hSupport hRestClosed Old.toRelStructure
    r (fun (_ : Jset) (x : V) => x) hr hCopy hInverse

/-- Every line removed from a MINIMAL transverse family leaves
an actual U-closed native subattachment with an EXPLICIT protected
old-picture coordinate retraction. The removed line is constant
at that coordinate, so it is genuinely exceptional.

This is the exact combinatorial/rest-retraction part of a potential
multi-line free-cut argument. The missing source free-cut and
rank-j boundary compatibility must be proved separately. -/
theorem exists_minimal_transverse_native_rest_retractions_2019
    {rules : ClosureDescription L}
    [DecidableEq I]
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (hOld : IsUClosed rules Old.toRelStructure)
    (hSupport : IsUSubstructure rules Old.toRelStructure (Old.support alpha))
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power (Old.restrict alpha) N).toRelStructure A
      (power (Old.restrict alpha) N).part)
    (hWhole : IsUClosed rules
      (RelStructure.Attachment.attach Old.toRelStructure
        (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)))
    (S : Finset I)
    (hNoCommon : ¬ ∃ k : Fin N,
      ∀ i ∈ S, (lines i).symbol k = .parameter) :
    ∃ T : Finset I, T ⊆ S ∧
      (¬ ∃ k : Fin N,
        ∀ i ∈ T, (lines i).symbol k = .parameter) ∧
      (∀ i ∈ T, ∃ k : Fin N,
        (lines i).symbol k ≠ .parameter ∧
        IsClosedUHomomorphismEmbedding rules
          (selectedNativeHJAttachment2019
            Old alpha A hRestricted lines (T.erase i))
          Old.toRelStructure
          (selectedNativeHJCoordinateMap2019
            Old alpha (T.erase i) k)) := by
  obtain ⟨T, hSubset, hBad, hEraseCoord⟩ :=
    exists_minimal_noncommon_HJ_lines lines S hNoCommon
  refine ⟨T, hSubset, hBad, ?_⟩
  intro i hi
  obtain ⟨k, hNotParam, hRestParam⟩ := hEraseCoord i hi
  refine ⟨k, hNotParam, ?_⟩
  exact selectedNativeHJCoordinateMap2019_protected
    Old alpha A hRestricted lines hOld hSupport hPower hWhole
    (T.erase i) k hRestParam

end AllThoseRamseyClasses.Published
