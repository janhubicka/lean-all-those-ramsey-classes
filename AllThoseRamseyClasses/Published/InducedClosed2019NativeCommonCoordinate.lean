import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosurePictureCoordinate

/-!
# 2019 Lemma 2.30: complete actual native Hales--Jewett
# common-coordinate rank branch in the corrected paper semantics

The pinned partite-construction library proves a genuine finite
Hales--Jewett history fact: when all exterior lines visited by the
generators of an exact tested structure admit one common parameter
coordinate k, evaluate the core at k and the selected old copies
identically. The resulting retraction transfers the old rank-n
completion invariant to the ORIGINAL tested source.

This file instantiates that REAL native construction in the
paper-faithful corrected Definition 2.15/2.17 completion convention.
The tested source may be non-U-closed and its carrier is not enlarged.
Its rank/generator budget is G.card<=n. Only the intermediate target
hulls inside the closed Old picture may add closure outputs.

The assumption about the common variable coordinate is LOCAL to
the tested structure's generator-active line indices, not global
over all Hales--Jewett lines (which would destroy the Ramsey lemma).

This verifies one meaningful branch of the higher-rank Picture
step, but not the genuinely transverse multi-line case, the
unrestricted initial repair or corrected Theorem 2.18.
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

/-- For any genuine native Hales--Jewett subattachment whose
generator-active lines share a parameter coordinate, the ORIGINAL
finite (possibly weak) tested structure has an amended 2019
(K,U)-completion. The existing old rank-n premise is stated using
the paper's exact induced closed-test completion convention.

This is a constructor-based native-history theorem, not an
abstract invented retraction or a strict rank increment. -/
theorem inducedClosed2019_native_common_coordinate_completion
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
    (hSize : G.card ≤ n) (k : Fin N)
    (hActive : ∀ g ∈ G, ∀ i,
      RelStructure.Attachment.OutsideAt (Old.support alpha) i (e g) →
        (lines i).symbol k = .parameter) :
    HasInducedClosedUKCompletion K rules Test := by
  have hAbstractRank :
      ∀ (T : Set V) [Fintype T],
        IsUClosed rules (Old.toRelStructure.induce T) →
        USize rules (Old.toRelStructure.induce T) ≤ n →
          HasClosedUKCompletion K rules (Old.toRelStructure.induce T) := by
    intro T hFiniteT hClosedT hSizeT
    letI : Fintype T := hFiniteT
    exact (inducedClosedKCompletion_iff_abstract_2019).mp
      (hRank T hClosedT hSizeT)
  have hNative : HasClosedUKCompletion K rules Test :=
    completion_of_common_generator_coordinate
      Old alpha A hRestricted lines hOld hSupport hPower hWhole
      n hAbstractRank Test e G hGen hSize k hActive
  exact (inducedClosedKCompletion_iff_abstract_2019).mpr hNative

end AllThoseRamseyClasses.Published
