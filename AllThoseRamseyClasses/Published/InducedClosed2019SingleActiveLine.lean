import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosurePictureCoordinate

/-!
# 2019 Lemma 2.30: actual native Hales--Jewett zero/one-line branches

In the native line-indexed Picture attachment, a generating test
whose exterior vertices come from at most ONE attached copy can be
completed over the previous closed picture by choosing a variable
coordinate of that line. No fixed parameter coordinate is required
for the entire Hales--Jewett Ramsey family (which would be false).

We give the corrected 2019 Definition 2.15 completion conclusion
on the EXACT original weak source. The pinned library supplies the
real coordinate-retraction construction. Its input completion
predicate is the abstract embedded closed-test convention, and the
previously Lean-proved normalization translates it to the proposed
2019 induced closed-test convention without a new hypothesis.

The no-exterior-generator case also works directly in every native
positive power: the selected subhistory contains only the core.

This proves two genuine history branches. It does not handle
two or more generator-active lines with disjoint parameter sets,
or the full j->j+1 rank increment.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Partite
open StructuralRamsey.Partite.Induced
open StructuralRamsey.HalesJewett

universe u v
variable {L : RelLanguage.{u}}
variable {P Q V I X : Type v} {N : ℕ}

/-- A native source whose generator-active private vertices
all come from ONE designated line i0 has a corrected completion
from the old rank-n hypothesis. The line's own parameter set
is nonempty; all other lines may have incompatible parameters. -/
theorem inducedClosed2019_native_single_active_line_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    [Finite V] [DecidableEq V]
    (hOld : IsUClosed rules Old.toRelStructure)
    (hSupport : IsUSubstructure rules Old.toRelStructure (Old.support alpha))
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power (Old.restrict alpha) N).toRelStructure A
      (power (Old.restrict alpha) N).part)
    (hWhole : IsUClosed rules
      (RelStructure.Attachment.attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)))
    (n : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (Old.toRelStructure.induce T) →
      USize rules (Old.toRelStructure.induce T) ≤ n →
        HasInducedClosedUKCompletion K rules (Old.toRelStructure.induce T))
    (Test : RelStructure L X)
    (e : RelStructure.Embedding Test
      (RelStructure.Attachment.attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)))
    (G : Finset X) (hGen : IsUGenerating rules Test (↑G : Set X))
    (hSize : G.card ≤ n)
    (i0 : I)
    (hOnlyLine : ∀ g ∈ G, ∀ i,
      RelStructure.Attachment.OutsideAt (Old.support alpha) i (e g) →
        i = i0) :
    HasInducedClosedUKCompletion K rules Test := by
  obtain ⟨k, hk⟩ := (lines i0).hasParameter
  have hRankAbstract :
      ∀ (T : Set V) [Fintype T],
        IsUClosed rules (Old.toRelStructure.induce T) →
        USize rules (Old.toRelStructure.induce T) ≤ n →
          HasClosedUKCompletion K rules (Old.toRelStructure.induce T) := by
    intro T hFT hT hSizeT
    letI : Fintype T := hFT
    exact (inducedClosedKCompletion_iff_abstract_2019).mp
      (hRank T hT hSizeT)
  have hSelected :
      ∀ g ∈ G, ∀ i,
        RelStructure.Attachment.OutsideAt (Old.support alpha) i (e g) →
          (lines i).symbol k = .parameter := by
    intro g hg i hOut
    rw [hOnlyLine g hg i hOut]
    exact hk
  have hNative : HasClosedUKCompletion K rules Test :=
    completion_of_common_generator_coordinate
      Old alpha A hRestricted lines hOld hSupport hPower hWhole
      n hRankAbstract Test e G hGen hSize k hSelected
  exact (inducedClosedKCompletion_iff_abstract_2019).mpr hNative

/-- If no generator meets any exterior old copy, a positive
Hales--Jewett coordinate is sufficient. Other nongenerating
vertices may still lie outside the core: the checked subhistory
lemma controls them without enlarging the tested source. -/
theorem inducedClosed2019_native_no_active_line_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (hN : 0 < N)
    [Finite V] [DecidableEq V]
    (hOld : IsUClosed rules Old.toRelStructure)
    (hSupport : IsUSubstructure rules Old.toRelStructure (Old.support alpha))
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power (Old.restrict alpha) N).toRelStructure A
      (power (Old.restrict alpha) N).part)
    (hWhole : IsUClosed rules
      (RelStructure.Attachment.attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)))
    (n : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (Old.toRelStructure.induce T) →
      USize rules (Old.toRelStructure.induce T) ≤ n →
        HasInducedClosedUKCompletion K rules (Old.toRelStructure.induce T))
    (Test : RelStructure L X)
    (e : RelStructure.Embedding Test
      (RelStructure.Attachment.attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)))
    (G : Finset X) (hGen : IsUGenerating rules Test (↑G : Set X))
    (hSize : G.card ≤ n)
    (hNoOutside : ∀ g ∈ G, ∀ i,
      ¬ RelStructure.Attachment.OutsideAt (Old.support alpha) i (e g)) :
    HasInducedClosedUKCompletion K rules Test := by
  let k : Fin N := ⟨0, hN⟩
  have hRankAbstract :
      ∀ (T : Set V) [Fintype T],
        IsUClosed rules (Old.toRelStructure.induce T) →
        USize rules (Old.toRelStructure.induce T) ≤ n →
          HasClosedUKCompletion K rules (Old.toRelStructure.induce T) := by
    intro T hFT hT hSizeT
    letI : Fintype T := hFT
    exact (inducedClosedKCompletion_iff_abstract_2019).mp
      (hRank T hT hSizeT)
  have hSelected :
      ∀ g ∈ G, ∀ i,
        RelStructure.Attachment.OutsideAt (Old.support alpha) i (e g) →
          (lines i).symbol k = .parameter := by
    intro g hg i hOut
    exact False.elim (hNoOutside g hg i hOut)
  have hNative : HasClosedUKCompletion K rules Test :=
    completion_of_common_generator_coordinate
      Old alpha A hRestricted lines hOld hSupport hPower hWhole
      n hRankAbstract Test e G hGen hSize k hSelected
  exact (inducedClosedKCompletion_iff_abstract_2019).mpr hNative

end AllThoseRamseyClasses.Published
