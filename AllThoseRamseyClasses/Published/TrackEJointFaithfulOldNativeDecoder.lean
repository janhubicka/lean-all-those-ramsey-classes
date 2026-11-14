import AllThoseRamseyClasses.Published.TrackEHybridOldDecoderUnique
import AllThoseRamseyClasses.Published.TrackEJointOldDecoderNativeRoundtrip

/-!
# Track E2: value-faithful, domain-faithful native OLD decoder

This is the next actual integration step of the corrected 2019
hybrid construction, on its ORIGINAL unchanged vertex carrier.

The merged cross-pattern fibre theorem and OLD decoder uniqueness
(#1169/#1177/#1179) show that the complete OLD output value
set of F(xs) is independent of both:
* the surjective distinct-root equality-pattern enumeration; and
* the order/mask of its complete set of output parts.

The exact joint U-closed/no-defined-empty work (#1165/#1168)
and the independent OLD domain-decoder bridge (#1180, parent)
show that the chosen partial decoder is defined exactly on
original OLD active domain records. No activated mask can claim
a defined-empty native value.

This module combines them. A single precise SPLIT positive-value
cross-pattern invariant suffices in addition to the merged
`HybridJointNoEmptyNormal` class.

The resulting statements are about the *existing* ORIGINAL
OLD `wholeMaskPartialDecode` and its `collapseDomain`.
They give:
1. unconditional uniqueness of all whole value witnesses,
   under the explicit hybrid coherence predicates;
2. `some U` iff a complete OLD witness of U is visible;
3. exact native/nonempty-partial roundtrip on the same carrier;
4. when the joint target is U-closed and original arities positive,
   domain-mask activity iff the partial decoder is defined;
5. the native fibre is exactly U for any displayed complete
   original OLD value witness and is empty iff the OLD input
   domain is inactive.

No new target vertices, closure hull, alternative decoder,
normality of arbitrary weak (non-U-closed) Pictures, or
finite-family ordered sparse Ramsey theorem is asserted.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.Structure.TrackENativePartialFullFaithfulness

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Every pair of complete OLD function-value witnesses on the
ACTUAL hybrid target names the SAME SET of output vertices,
regardless of original input equality-pattern or complete mask.
Only the strict-normality clauses and positive split output
cross-pattern transport are used here, not U-closedness. -/
theorem HybridJointNoEmptyNormal.oldDecoder_uniqueValue_of_split
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hSplit : HybridSplitOutputPatternTransport
      (splitMaskJointRootReduct C))
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V)
    (U T : Set V)
    (hU : HasWholeMaskValue
      (splitMaskHybridOriginalOldReduct (splitMaskJointRootReduct C))
      F xs U)
    (hT : HasWholeMaskValue
      (splitMaskHybridOriginalOldReduct (splitMaskJointRootReduct C))
      F xs T) :
    U = T :=
  hNorm.normal.coherent.oldDecoder_uniqueValue
    hNorm.normal.positive
    hNorm.normal.injectiveDomains
    hNorm.normal.originalMasks hSplit F xs U T hU hT

/-- `wholeMaskPartialDecode` chooses a complete OLD value only
when it is literally displayed, and realizes ALL displayed values:
the choice is independent of every input/mask presentation. -/
theorem HybridJointNoEmptyNormal.oldDecoder_func_some_iff_of_split
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hSplit : HybridSplitOutputPatternTransport
      (splitMaskJointRootReduct C))
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V)
    (U : Set V) :
    ((splitMaskHybridOriginalOldReduct
      (splitMaskJointRootReduct C)).wholeMaskPartialDecode).func
        F xs = some U ↔
    HasWholeMaskValue
      (splitMaskHybridOriginalOldReduct (splitMaskJointRootReduct C))
      F xs U :=
  hNorm.normal.coherent.oldDecoder_func_some_iff
    hNorm.normal.positive
    hNorm.normal.injectiveDomains
    hNorm.normal.originalMasks hSplit F xs U

/-- This SAME partial decoder never has a defined-empty value,
since every displayed positive OLD whole tuple has a genuine
nonempty output mask. The cross-pattern uniqueness conclusion
is now discharged, rather than postulated. -/
theorem HybridJointNoEmptyNormal.oldDecoder_noDefinedEmpty_of_split
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hSplit : HybridSplitOutputPatternTransport
      (splitMaskJointRootReduct C)) :
    NoDefinedEmptyValues
      ((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode) :=
  hNorm.oldDecoder_noDefinedEmpty_of_unique
    (fun F xs U T hU hT =>
      hNorm.oldDecoder_uniqueValue_of_split
        hSplit F xs U T hU hT)

/-- The decoded OLD native `Structure` and its nonempty-partial
encoding recover the SAME original Option(Set) partial structure
on exactly the SAME vertex carrier. No native model is chosen
independently and no defined-empty input is erased. -/
theorem HybridJointNoEmptyNormal.oldDecoder_nativeRoundtrip_of_split
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hSplit : HybridSplitOutputPatternTransport
      (splitMaskJointRootReduct C)) :
    (((splitMaskHybridOriginalOldReduct
      (splitMaskJointRootReduct C)).wholeMaskPartialDecode).collapseDomain).toNonemptyPartial =
    (splitMaskHybridOriginalOldReduct
      (splitMaskJointRootReduct C)).wholeMaskPartialDecode :=
  hNorm.oldDecoder_nativeRoundtrip_of_unique
    (fun F xs U T hU hT =>
      hNorm.oldDecoder_uniqueValue_of_split
        hSplit F xs U T hU hT)

/-- Every displayed complete OLD function value is literally
the set-valued function fibre of the native collapse of the
same OLD decoder. There is NO new output witness construction:
the actual existing partial decoder already chooses this value,
and `collapseDomain` forgets only its now-proven faithful bit. -/
theorem HybridJointNoEmptyNormal.oldNativeFibre_eq_of_wholeValue
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hSplit : HybridSplitOutputPatternTransport
      (splitMaskJointRootReduct C))
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V)
    (U : Set V)
    (hValue : HasWholeMaskValue
      (splitMaskHybridOriginalOldReduct (splitMaskJointRootReduct C))
      F xs U) :
    (((splitMaskHybridOriginalOldReduct
      (splitMaskJointRootReduct C)).wholeMaskPartialDecode).collapseDomain).func
      F xs = U := by
  have hSome :
      ((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode).func
          F xs = some U :=
    (hNorm.oldDecoder_func_some_iff_of_split
      hSplit F xs U).mpr hValue
  change (((splitMaskHybridOriginalOldReduct
      (splitMaskJointRootReduct C)).wholeMaskPartialDecode).func
      F xs).getD ∅ = U
  simp only [hSome, Option.getD_some]

/-- ACTUAL native function fibre emptiness is equivalent to
inactivity of every complete OLD mask-domain record for the
primitive input, provided the target is JOINT U-closed and the
primitive function has positive arity. The proof needs actual
value uniqueness and no-defined-empty values: otherwise the
partial decoder could have a `some ∅` fibre. -/
theorem HybridJointNoEmptyNormal.oldNativeFibre_empty_iff_noDomain
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hClosed : IsUClosed (L.splitMaskJointClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hSplit : HybridSplitOutputPatternTransport
      (splitMaskJointRootReduct C))
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V) :
    (((splitMaskHybridOriginalOldReduct
      (splitMaskJointRootReduct C)).wholeMaskPartialDecode).collapseDomain).func
      F xs = ∅ ↔
    ¬ HasWholeMaskDomain
      (splitMaskHybridOriginalOldReduct (splitMaskJointRootReduct C))
      F xs := by
  constructor
  · intro hEmpty hDomain
    obtain ⟨U, hValue⟩ :=
      (hNorm.oldDomain_iff_hasWholeValue hClosed hPos F xs).mp
        hDomain
    have hFibre : (((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode).collapseDomain).func
          F xs = U :=
      hNorm.oldNativeFibre_eq_of_wholeValue hSplit F xs U hValue
    have hSome :
        ((splitMaskHybridOriginalOldReduct
          (splitMaskJointRootReduct C)).wholeMaskPartialDecode).func
            F xs = some U :=
      (hNorm.oldDecoder_func_some_iff_of_split hSplit F xs U).mpr
        hValue
    obtain ⟨y, hy⟩ :=
      hNorm.oldDecoder_noDefinedEmpty_of_split hSplit F xs U hSome
    have hUEmpty : U = (∅ : Set V) := hFibre.symm.trans hEmpty
    rw [hUEmpty] at hy
    exact Set.not_mem_empty y hy
  · intro hNoDomain
    have hNone :
        ((splitMaskHybridOriginalOldReduct
          (splitMaskJointRootReduct C)).wholeMaskPartialDecode).func
          F xs = none :=
      (hNorm.oldDecoder_none_iff_noDomain hClosed hPos F xs).mpr
        hNoDomain
    change (((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode).func
        F xs).getD ∅ = ∅
    simp only [hNone, Option.getD_none]

/-- Integrated, strong but PRE-RAMSEY native OLD decoding contract.
The same original tagged target `C` has:
(1) exactly the old complete-value relation as its partial graph;
(2) exactly the OLD active domain relation as its definedness;
(3) no defined-empty values, hence an exact native roundtrip.

This conditional theorem combines the already certified
cross-pattern fibre coherence with the independent joint
U-closed OLD-domain proof. It does not assert that an arbitrary
two-pass sparse Picture meets its hypotheses. -/
theorem HybridJointNoEmptyNormal.oldDecoder_faithfulNative_contract
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hClosed : IsUClosed (L.splitMaskJointClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hSplit : HybridSplitOutputPatternTransport
      (splitMaskJointRootReduct C)) :
    (∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V)
      (U : Set V),
      ((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode).func
          F xs = some U ↔
      HasWholeMaskValue
        (splitMaskHybridOriginalOldReduct (splitMaskJointRootReduct C))
        F xs U) ∧
    (∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V),
      ((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode).func
          F xs = none ↔
      ¬ HasWholeMaskDomain
        (splitMaskHybridOriginalOldReduct (splitMaskJointRootReduct C))
        F xs) ∧
    ((((splitMaskHybridOriginalOldReduct
      (splitMaskJointRootReduct C)).wholeMaskPartialDecode).collapseDomain).toNonemptyPartial =
      (splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode) ∧
    NoDefinedEmptyValues
      ((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F xs U
    exact hNorm.oldDecoder_func_some_iff_of_split hSplit F xs U
  · intro F xs
    exact hNorm.oldDecoder_none_iff_noDomain hClosed hPos F xs
  · exact hNorm.oldDecoder_nativeRoundtrip_of_split hSplit
  · exact hNorm.oldDecoder_noDefinedEmpty_of_split hSplit

end StructuralRamsey.RelStructure
