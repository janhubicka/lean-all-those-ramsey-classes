import AllThoseRamseyClasses.Published.MinimalTransverseNativeRetract2019
import AllThoseRamseyClasses.Published.NativePowerCoordinateParts2019

/-!
# Minimal transverse Hales--Jewett history: TWO actual side retractions

The actual native Picture supplies more than a coordinate witness:

For any finite generator-active line family without a common variable
coordinate, choose a minimal obstructing subfamily T. For EACH i∈T:
  * k_rest is a parameter for all the lines other than i,
    but is a constant coordinate on line i;
  * k_one is a parameter of the exceptional line i itself;
  * the selected REST subattachment (lines T.erase i) has an
    actual protected coordinate/identity retraction into Old
    using k_rest, and the SINGLE exception subattachment
    (line {i}) has its own actual protected retraction using k_one;
  * although these maps need not agree as vertices on the
    common power core, they agree after applying Old.part.

The coordinate facts are certified in the minimal bad-line theorem.
Both side maps are certified by genuine native closed-support
attachment/fold constructions. Core part compatibility is certified
directly from power vertex belongs, not from arbitrary K-completions.

This is a concrete TWO-SIDE map configuration. It does NOT yet prove
that the tested rank-(j+1) closed source admits a proper free
decomposition into these sides, nor that the common projected
part labels lift to a shared closed K-boundary through full
embeddings of A. Those are exactly the remaining rank-gluing
obligations. No unconditional general Theorem 2.18 is claimed.
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

/-- The actual two sides of a minimal transverse line family
have protected old-picture retractions at their own parameter
coordinates, compatible at the old part-label level on the
ENTIRE shared native power core. No side K-completion target,
source free cut, or root embedding is guessed here. -/
theorem exists_minimal_transverse_two_side_part_retractions_2019
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
      (¬ ∃ k : Fin N, ∀ i ∈ T,
        (lines i).symbol k = .parameter) ∧
      (∀ i ∈ T, ∃ kRest kOne : Fin N,
        (lines i).symbol kRest ≠ .parameter ∧
        (lines i).symbol kOne = .parameter ∧
        IsClosedUHomomorphismEmbedding rules
          (selectedNativeHJAttachment2019
            Old alpha A hRestricted lines (T.erase i))
          Old.toRelStructure
          (selectedNativeHJCoordinateMap2019
            Old alpha (T.erase i) kRest) ∧
        IsClosedUHomomorphismEmbedding rules
          (selectedNativeHJAttachment2019
            Old alpha A hRestricted lines {i})
          Old.toRelStructure
          (selectedNativeHJCoordinateMap2019
            Old alpha {i} kOne) ∧
        (∀ z : NonInduced.Vertex (Old.restrict alpha) N,
          Old.part (z.coord kRest).1 =
            Old.part (z.coord kOne).1)) := by
  obtain ⟨T, hSubset, hBad, hLocal⟩ :=
    exists_minimal_noncommon_HJ_lines lines S hNoCommon
  refine ⟨T, hSubset, hBad, ?_⟩
  intro i hi
  obtain ⟨kRest, hNot, hParamRest⟩ := hLocal i hi
  obtain ⟨kOne, hParamOne⟩ := (lines i).hasParameter
  have hRest :
      IsClosedUHomomorphismEmbedding rules
        (selectedNativeHJAttachment2019
          Old alpha A hRestricted lines (T.erase i))
        Old.toRelStructure
        (selectedNativeHJCoordinateMap2019
          Old alpha (T.erase i) kRest) :=
    selectedNativeHJCoordinateMap2019_protected
      Old alpha A hRestricted lines hOld hSupport
      hPower hWhole (T.erase i) kRest hParamRest
  have hSingle :
      IsClosedUHomomorphismEmbedding rules
        (selectedNativeHJAttachment2019
          Old alpha A hRestricted lines {i})
        Old.toRelStructure
        (selectedNativeHJCoordinateMap2019
          Old alpha {i} kOne) := by
    apply selectedNativeHJCoordinateMap2019_protected
      Old alpha A hRestricted lines
      hOld hSupport hPower hWhole {i} kOne
    intro q hq
    have hqi : q = i := Finset.mem_singleton.mp hq
    subst q
    exact hParamOne
  refine ⟨kRest, kOne, hNot, hParamOne, hRest, hSingle, ?_⟩
  intro z
  exact nativePower_two_coordinates_old_parts_agree
    Old alpha N z kRest kOne

end AllThoseRamseyClasses.Published
