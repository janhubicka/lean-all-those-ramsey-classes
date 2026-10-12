import AllThoseRamseyClasses.Published.NativePositiveGeneratorIndices2019
import AllThoseRamseyClasses.Published.NativeClosedPictureWeakRest2019

/-!
# Exact weak tests of the published Picture have <= U-rank many active lines

The newly verified native positive generator-index estimate (PR #160)
is phrased on ANY finite weak source with a positive homomorphism into
the true native attachment. The corrected 2019 higher-rank Picture
has a protected positive projection from the FULL source, and each
(4c) test is an EXACT induced weak vertex subset, possibly nonclosed.

This paper-faithful bridge restricts the full corrected projection
to that EXACT weak test and applies the positive active-line counting
lemma. The result needs only the actual old attaching support to be
relatively U-closed; it does NOT ask that the exact test be closed or
the full projection globally injective.

For every original exact finite weak test T,
 |genuine private-active attachment copies met by T|
          <= USize(T).

The bound is on actual history copy-index cardinality, not the sizes
of closed side completions. It does not produce a common parameter
coordinate, a closed K-boundary, or an unconditional strict
j->j+1 Picture constructor. The repaired Theorem 2.18 remains OPEN.
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

/-- The EXACT weak induced tested source of the corrected 2019 Picture
visits no more distinct genuine private-active Hales--Jewett lines
than its intrinsic U-generating rank. This works even for an
arbitrary NONINJECTIVE protected full-Picture projection. -/
theorem native2019_protected_picture_exact_weak_active_le_USize
    {rules : ClosureDescription L}
    {P Q V U I : Type v} {N : ℕ}
    [Finite U]
    (C : RelStructure L U)
    (Old : System L P V)
    (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (hSupport : IsUSubstructure rules Old.toRelStructure
      (Old.support alpha))
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (p : U → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I))
    (hp : IsInducedClosedUHomomorphismEmbedding rules C
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p)
    (T : Finset U) :
    (native2019_exact_active_index_finset
      (Old.support alpha) (fun x : (↑T : Set U) => p x.1)).card ≤
      USize rules (C.induce (↑T : Set U)) := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  have hpT : (C.induce (↑T : Set U)).IsHomomorphism
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines))
      (fun x : (↑T : Set U) => p x.1) := by
    intro R xs hxs
    exact hp.1 R (fun i => (xs i).1) hxs
  exact native2019_positive_active_index_card_le_USize
    (C.induce (↑T : Set U))
    Old.toRelStructure (Old.support alpha)
    (power (Old.restrict alpha) N).toRelStructure
    (closureLineMaps Old alpha A hRestricted lines)
    hSupport (fun x : (↑T : Set U) => p x.1) hpT

end AllThoseRamseyClasses.Published
