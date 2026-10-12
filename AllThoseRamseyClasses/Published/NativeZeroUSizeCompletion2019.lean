import AllThoseRamseyClasses.Published.NativePositiveGeneratorIndices2019
import AllThoseRamseyClasses.Published.NativeProtectedZeroActive2019

/-!
# Native Hales--Jewett zero-U-rank weak source always completes in A

The corrected 2019 Lemma 2.30 must also handle NONMAXIMAL intrinsic
U-rank exact weak tests. The strengthened native generator history
bound from PR #160 counts true PRIVATE-active old-copy indices under
merely POSITIVE maps, without global projection injectivity:

    |Active(Source,p)| <= USize(Source).

At USize(Source)=0 there are NO private-active indices. The genuine
protected source map (not just positivity) therefore lands entirely
in the embedded native power core. Its protected core factorization
composes with power.part to the fixed original closed irreducible
A in K (merged PR #154).

Hence ANY exact weak source of ZERO intrinsic U-size, regardless of
the potentially enormous number of closure-output vertices and
without assuming the source U-closed, has a genuine corrected
K-completion in A. No old W_j, R_j or rooted W_j^A induction
premise is needed.

This is one real nonmaximal-rank completion case of the outstanding
higher-rank Picture theorem. Positive USize 1 and above with exterior
active lines and transverse A-root gluing remain open.
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

/-- An exact weak source of intrinsic U-generating rank ZERO with a
corrected protected map into an ACTUAL native HJ attachment has
a corrected K-completion into the specified A∈K, provided the
old attaching support is relatively U-closed.

No finite source-vertex-size bound is assumed; zero rank may produce
many vertices by closure from the empty generator set. -/
theorem native2019_protected_zero_USize_has_A_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {P Q V U I : Type v} {N : ℕ}
    [Fintype U] [Finite Q]
    (Source : RelStructure L U)
    (hZero : USize rules Source = 0)
    (Old : System L P V)
    (alpha : Q ↪ P) (A : RelStructure L Q)
    (hAK : K A) (hAIrred : A.Irreducible)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (hSupport : IsUSubstructure rules Old.toRelStructure
      (Old.support alpha))
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power (Old.restrict alpha) N).toRelStructure A
      (power (Old.restrict alpha) N).part)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (p : U → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I))
    (hp : IsInducedClosedUHomomorphismEmbedding rules Source
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p) :
    HasInducedClosedUKCompletion K rules Source := by
  classical
  have hActiveBound :=
    native2019_positive_active_index_card_le_USize
      Source Old.toRelStructure (Old.support alpha)
      (power (Old.restrict alpha) N).toRelStructure
      (closureLineMaps Old alpha A hRestricted lines)
      hSupport p hp.1
  have hNoActive :
      native2019_exact_active_index_finset (Old.support alpha) p = ∅ := by
    apply Finset.card_eq_zero.mp
    omega
  have hNoPrivate : ∀ x : U, ∀ i : I,
      ¬ OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) i (p x) := by
    intro x i hout
    have hi :
        i ∈ native2019_exact_active_index_finset
          (Old.support alpha) p :=
      (native2019_mem_exact_active_index_iff
        (Old.support alpha) p i).mpr ⟨x, hout⟩
    simp [hNoActive] at hi
  exact native2019_protected_zero_active_has_A_completion
    Source Old alpha A hAK hAIrred
    hRestricted hPower lines p hp hNoPrivate

end AllThoseRamseyClasses.Published
