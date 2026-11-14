import AllThoseRamseyClasses.Published.TrackEJointOldDomainDecoderDefinedness
import PartiteConstruction.Functional.TrackENativePartialFullFaithfulness

/-!
# Track E2: native roundtrip for the strict-normal OLD whole-mask decoder

The corrected original OLD relational language can represent
`some ∅` (defined-empty) as distinct from `none` (undefined).
This extra partial syntax is not a native set-valued Structure.

The strict hybrid target-normality invariant rules out any
activated zero-width ORIGINAL OLD domain mask. Positive-output
soundness forces a displayed complete OLD output tuple to
activate its corresponding mask. Therefore EVERY complete OLD
output witness in a strict-normal hybrid target is nonempty.

Given the separately proved VALUE-uniqueness property of OLD
whole-mask witnesses, the existing `wholeMaskPartialDecode`
therefore has no defined-empty values. The already certified
native/partial full-faithfulness theorem then identifies it
EXACTLY with the nonempty partial encoding of its native
`collapseDomain` on the SAME original vertex carrier.

VALUE-uniqueness is deliberately an explicit premise here,
so this theorem is independent of the still-under-validation
cross-pattern fibre proof. Active OLD domain = definedness
comes from the preceding Track E2 module, not from this
roundtrip alone. No output vertex, generated closure hull or
independent target oracle is introduced.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.Structure.TrackENativePartialFullFaithfulness

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- If complete original values are UNIQUE for each primitive
input, strict target-normality excludes every defined-empty
value of the EXISTING OLD Option(Set) whole-mask decoder.
This proof uses positive-output soundness to relate a complete
tuple to its actual positive-width OLD domain mask. -/
theorem HybridJointNoEmptyNormal.oldDecoder_noDefinedEmpty_of_unique
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hUnique : ∀ (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → V)
      (U T : Set V),
      HasWholeMaskValue
        (splitMaskHybridOriginalOldReduct
          (splitMaskJointRootReduct C)) F xs U →
      HasWholeMaskValue
        (splitMaskHybridOriginalOldReduct
          (splitMaskJointRootReduct C)) F xs T →
      U = T) :
    NoDefinedEmptyValues
      ((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode) := by
  classical
  let Base : RelStructure (L.splitMaskHybrid Parts) V :=
    splitMaskJointRootReduct C
  let Old : RelStructure (L.wholeMaskPatternLanguage Parts) V :=
    splitMaskHybridOriginalOldReduct Base
  intro F xs U hSome
  have hValue : HasWholeMaskValue Old F xs U :=
    (Old.wholeMaskPartialDecode_func_some_iff
      F xs (hUnique F xs) U).mp hSome
  obtain ⟨m, r, hr, mask, t, hTuple, _hArgs, hSet⟩ := hValue
  let pat : FunctionInputPattern L := ⟨F, m, r, hr⟩
  have hOutput :
      Base.rel (hybridOriginalMaskOutputSymbol pat mask) t :=
    hTuple
  have hDomain :
      Base.rel (hybridOriginalMaskDomainSymbol pat mask)
        (fun i : Fin m => t (Fin.castAdd mask.size i)) :=
    hNorm.normal.positive.1 pat mask t hOutput
  have hMaskPositive : 0 < mask.size :=
    hNorm.noEmpty pat mask
      (fun i : Fin m => t (Fin.castAdd mask.size i)) hDomain
  let j : Fin mask.size := ⟨0, hMaskPositive⟩
  refine ⟨t (Fin.natAdd m j), ?_⟩
  rw [hSet]
  exact ⟨j, rfl⟩

/-- The existing full-faithfulness theorem says absence of
defined-empty values is equivalent to an EXACT NATIVE roundtrip.
The current OLD decoder therefore equals the nonempty partial
encoding of its own native collapse, provided unique OLD values
are already established. No choice of a new decoder is made. -/
theorem HybridJointNoEmptyNormal.oldDecoder_nativeRoundtrip_of_unique
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hUnique : ∀ (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → V)
      (U T : Set V),
      HasWholeMaskValue
        (splitMaskHybridOriginalOldReduct
          (splitMaskJointRootReduct C)) F xs U →
      HasWholeMaskValue
        (splitMaskHybridOriginalOldReduct
          (splitMaskJointRootReduct C)) F xs T →
      U = T) :
    (((splitMaskHybridOriginalOldReduct
      (splitMaskJointRootReduct C)).wholeMaskPartialDecode).collapseDomain)
        .toNonemptyPartial =
    (splitMaskHybridOriginalOldReduct
      (splitMaskJointRootReduct C)).wholeMaskPartialDecode := by
  exact
    (noDefinedEmpty_iff_nativeRoundtrip
      ((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode)).mp
      (hNorm.oldDecoder_noDefinedEmpty_of_unique hUnique)

end StructuralRamsey.RelStructure
