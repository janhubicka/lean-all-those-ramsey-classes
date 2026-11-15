import AllThoseRamseyClasses.Published.TrackEHybridOldMaskDomainDecoderIff

/-!
# Track E2: exact OLD whole-mask re-encoding on the original vertices

Previous Track E2 results established: (i) strict original-mask
domains correspond to the existing OLD Option(Set) decoder and its
literal unary part map, and (ii) every activated positive-mask
domain has exactly one complete ORIGINAL OLD output tuple in the
same exact JOINT U-closed target.

The remaining positive complete-output relation also reflects
the decoder's whole-value graph. Suppose an arbitrary tuple t
has an injective input root, its whole displayed output SET is
the actual decoded value at that primitive input, and each
output coordinate has its prescribed unary mask part. The exact
OLD domain-re-encoding theorem forces the relevant mask domain,
and literal joint U-closedness yields one ACTUAL old output tuple
t0 above that root. Both t and t0 list the SAME entire decoded
fibre and respect the SAME injective mask-part labelling; hence
the two output tuples agree coordinatewise. Their input
prefixes already agree, so t = t0 and the positive OLD graph
relation for t was genuinely present.

Together with the already-certified positive-output soundness
direction this gives a full iff between the ACTUAL complete
OLD output relation and the canonical complete-value graph of
the EXISTING OLD decoder, with no new vertex or independent
function-value choice.

The second theorem packages both exact OLD domain and output
relations as an actual equality of relational structures:
`splitMaskHybridOriginalOldReduct E =
 (splitMaskHybridOriginalOldReduct E).wholeMaskPartialDecode
   |>.wholeMaskPatternGraph actualPartMap`.

This exact re-encoding concerns the ORIGINAL OLD mask graph,
not yet the nested OLD root tags, per-part split relations or
all fresh JOINT full-hybrid-root tag names. The finite-family
two-pass ordered sparse Ramsey construction remains open.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The ACTUAL positive ORIGINAL OLD complete-output relation
is exactly the complete-mask graph relation of the EXISTING
chosen OLD partial-function decoder on the SAME vertex carrier.
The reverse direction uses positive-root joint U-closure and
exact same-part fibre equality; it does not insert missing
outputs or take a generated hull. -/
theorem HybridJointNoEmptyNormal.originalMaskOutput_iff_oldDecoded
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hClosed : IsUClosed (L.splitMaskJointClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hSplit : HybridSplitOutputPatternTransport
      (splitMaskJointRootReduct C))
    (hSaturated : HybridOriginalMaskDomainSaturated
      (splitMaskJointRootReduct C))
    (p : FunctionInputPattern L)
    (mask : CompleteOutputParts Parts)
    (t : Fin (p.rootSize + mask.size) → V) :
    (splitMaskJointRootReduct C).rel
        (hybridOriginalMaskOutputSymbol p mask) t ↔
      Function.Injective
        (fun i : Fin p.rootSize =>
          t (Fin.castAdd mask.size i)) ∧
      ((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode).func
          p.symbol
          ((fun i : Fin p.rootSize =>
            t (Fin.castAdd mask.size i)) ∘ p.argMap) =
        some (Set.range (fun j : Fin mask.size =>
          t (Fin.natAdd p.rootSize j))) ∧
      (∀ j : Fin mask.size,
        hNorm.normal.coherent.1.2.2.2.partMap
          (t (Fin.natAdd p.rootSize j)) = mask.label j) := by
  classical
  let Base : RelStructure (L.splitMaskHybrid Parts) V :=
    splitMaskJointRootReduct C
  let Old : RelStructure (L.wholeMaskPatternLanguage Parts) V :=
    splitMaskHybridOriginalOldReduct Base
  let part : V → Parts :=
    hNorm.normal.coherent.1.2.2.2.partMap
  let root : Fin p.rootSize → V :=
    fun i => t (Fin.castAdd mask.size i)
  let U : Set V := Set.range
    (fun j : Fin mask.size => t (Fin.natAdd p.rootSize j))
  constructor
  · intro hActual
    have hDomain :
        Base.rel (hybridOriginalMaskDomainSymbol p mask) root :=
      hNorm.normal.positive.1 p mask t hActual
    have hRootInj : Function.Injective root :=
      hNorm.normal.injectiveDomains.1 p mask root hDomain
    have hHas : HasWholeMaskValue Old p.symbol
        (root ∘ p.argMap) U := by
      refine ⟨p.rootSize, p.argMap, p.onto, mask,
        t, hActual, ?_, rfl⟩
      intro i
      rfl
    have hDecoded :
        (Old.wholeMaskPartialDecode).func p.symbol
          (root ∘ p.argMap) = some U :=
      (hNorm.normal.coherent.oldDecoder_func_some_iff
        hNorm.normal.positive hNorm.normal.injectiveDomains
        hNorm.normal.originalMasks hSplit
        p.symbol (root ∘ p.argMap) U).mpr hHas
    have hLabels (j : Fin mask.size) :
        part (t (Fin.natAdd p.rootSize j)) = mask.label j :=
      hNorm.normal.coherent.1.2.2.2.partMap_eq_of_label
        (t (Fin.natAdd p.rootSize j)) (mask.label j)
        (hNorm.normal.positive.2.2.2 p mask j t hActual)
    exact ⟨hRootInj, hDecoded, hLabels⟩
  · rintro ⟨hRootInj, hDecoded, hLabels⟩
    have hOutputPartSet :
        part '' U = Set.range mask.label := by
      ext q
      constructor
      · rintro ⟨y, ⟨j, rfl⟩, hy⟩
        exact ⟨j, (hLabels j).symm.trans hy⟩
      · rintro ⟨j, hj⟩
        exact ⟨t (Fin.natAdd p.rootSize j),
          ⟨j, rfl⟩, (hLabels j).trans hj⟩
    have hMask :
        Base.rel (hybridOriginalMaskDomainSymbol p mask) root :=
      (hNorm.originalMaskDomain_iff_oldDecoded
        hClosed hPos hSplit hSaturated p mask root).mpr
        ⟨hRootInj, U, hDecoded, hOutputPartSet⟩
    have hRootPositive : 0 < p.rootSize := by
      have hNe : p.rootSize ≠ 0 := by
        intro hz
        have i : Fin 0 :=
          hz ▸ p.argMap (⟨0, hPos p.symbol⟩ :
            Fin (L.funcArity p.symbol))
        exact i.elim0
      exact Nat.pos_of_ne_zero hNe
    obtain ⟨t0, ⟨hActual0, hPrefix0⟩, _⟩ :=
      hNorm.originalMask_hasUniqueFullOutput
        hClosed p mask root hRootPositive hMask
    let U0 : Set V := Set.range
      (fun j : Fin mask.size => t0 (Fin.natAdd p.rootSize j))
    have hHas0 : HasWholeMaskValue Old p.symbol
        (root ∘ p.argMap) U0 := by
      refine ⟨p.rootSize, p.argMap, p.onto, mask,
        t0, hActual0, ?_, rfl⟩
      intro i
      exact (hPrefix0 (p.argMap i)).symm
    have hDecoded0 :
        (Old.wholeMaskPartialDecode).func p.symbol
          (root ∘ p.argMap) = some U0 :=
      (hNorm.normal.coherent.oldDecoder_func_some_iff
        hNorm.normal.positive hNorm.normal.injectiveDomains
        hNorm.normal.originalMasks hSplit
        p.symbol (root ∘ p.argMap) U0).mpr hHas0
    have hSameFibre : U = U0 :=
      Option.some.inj (hDecoded.symm.trans hDecoded0)
    have hLabels0 (j : Fin mask.size) :
        part (t0 (Fin.natAdd p.rootSize j)) = mask.label j :=
      hNorm.normal.coherent.1.2.2.2.partMap_eq_of_label
        (t0 (Fin.natAdd p.rootSize j)) (mask.label j)
        (hNorm.normal.positive.2.2.2 p mask j t0 hActual0)
    have hOutEq (j : Fin mask.size) :
        t (Fin.natAdd p.rootSize j) =
          t0 (Fin.natAdd p.rootSize j) := by
      have hy : t (Fin.natAdd p.rootSize j) ∈ U0 := by
        rw [← hSameFibre]
        exact ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := hy
      have hjk : j = k := mask.label_injective (by
        calc
          mask.label j = part (t (Fin.natAdd p.rootSize j)) :=
            (hLabels j).symm
          _ = part (t0 (Fin.natAdd p.rootSize k)) :=
            congrArg part hk.symm
          _ = mask.label k := hLabels0 k)
      calc
        t (Fin.natAdd p.rootSize j) =
            t0 (Fin.natAdd p.rootSize k) := hk.symm
        _ = t0 (Fin.natAdd p.rootSize j) :=
          congrArg
            (fun j' : Fin mask.size => t0 (Fin.natAdd p.rootSize j'))
            hjk.symm
    have hPrefixEq (i : Fin p.rootSize) :
        t (Fin.castAdd mask.size i) =
          t0 (Fin.castAdd mask.size i) :=
      (hPrefix0 i).symm
    have hTupleEq : t = t0 := by
      funext k
      exact Fin.addCases hPrefixEq hOutEq k
    rw [hTupleEq]
    exact hActual0

/-- The entire ACTUAL ORIGINAL OLD domain+whole-output reduct
of the noncanonical hybrid target is LITERALLY the canonical
complete-mask graph of the EXISTING chosen OLD Option(Set)
decoder using its ACTUAL unique unary part map.

This equality reconstructs every named OLD mask predicate,
not just its existential domain bit and not merely the set of
positive OLD values. No additional vertices, function values,
part labels or canonical-root tags are generated.

It does NOT reconstruct inner/outer tags or singleton split
relations; those are separate stages of full hybrid re-encoding. -/
theorem HybridJointNoEmptyNormal.originalOldReduct_eq_decodedGraph
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hClosed : IsUClosed (L.splitMaskJointClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hSplit : HybridSplitOutputPatternTransport
      (splitMaskJointRootReduct C))
    (hSaturated : HybridOriginalMaskDomainSaturated
      (splitMaskJointRootReduct C)) :
    splitMaskHybridOriginalOldReduct (splitMaskJointRootReduct C) =
      (((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode).wholeMaskPatternGraph
          hNorm.normal.coherent.1.2.2.2.partMap) := by
  apply RelStructure.rel_injective
  funext R xs
  apply propext
  rcases R with R | R
  · exact Iff.rfl
  · rcases R with ⟨p, mask⟩ | ⟨p, mask⟩
    · exact hNorm.originalMaskDomain_iff_oldDecoded
        hClosed hPos hSplit hSaturated p mask xs
    · exact hNorm.originalMaskOutput_iff_oldDecoded
        hClosed hPos hSplit hSaturated p mask xs

end StructuralRamsey.RelStructure
