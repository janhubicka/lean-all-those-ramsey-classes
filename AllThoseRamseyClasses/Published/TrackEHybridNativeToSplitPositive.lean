import AllThoseRamseyClasses.Published.TrackEHybridOldDecoderUnique
import AllThoseRamseyClasses.Published.TrackEHybridNoDefinedEmptyMask
import PartiteConstruction.Structure.Relationalize

/-!
# Track E2: decoded native output vertices force positive split incidences

The forward direction, every visible singleton split incidence has
an ORIGINAL complete OLD witness under exact joint U-closedness,
is a separate Track E2 proof.

This module proves the complementary, independent reverse
direction. Suppose the ORIGINAL OLD decoder, collapsed to the
native set-valued Structure on the SAME vertex carrier, has
an output y in the fibre F(xs). If the input's displayed
equality-pattern root is genuinely injective and the unary
part predicate says that y has part q, then the hybrid source
must display the corresponding POSITIVE split (F,q)
output-incidence tuple with vertex y.

The proof does not simply postulate all split tuples. Decoder
membership first yields an actual positive complete OLD value
witness. The merged cross-pattern OLD decoder uniqueness theorem
ensures this witness has the chosen native fibre. The coordinate
representing y has the correct unary part label by positive
output soundness, and uniqueness of unary labels identifies it
with q. Visible whole/split SAME-VERTEX coherence produces a
positive split tuple on its original input-root enumeration.
The merged positive split SAME-VERTEX pattern transport then
moves that tuple to the requested injective equality-pattern
enumeration while preserving y.

No JOINT U-closedness or primitive arity positivity is needed
for THIS converse, since native membership already supplies
a complete OLD value witness. No output value, vertex, closure
hull, alternate decoder or finite-family Ramsey witness is made.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Any native OLD-decoded output y whose literal unary part is q
has a positive split (F,q) incidence on ANY injective
distinct-input equality-pattern enumeration of the same
primitive input tuple. The target part label is read directly
from the original hybrid unary predicate, including isolated
vertices and nullary input operations. -/
theorem HybridJointNoEmptyNormal.oldDecodedNative_mem_to_splitOutput
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hSplitTransport : HybridSplitOutputPatternTransport
      (splitMaskJointRootReduct C))
    (p : FunctionInputPattern L)
    (root : Fin p.rootSize → V)
    (hRootInj : Function.Injective root)
    (q : Parts) (y : V)
    (hPart : (splitMaskJointRootReduct C).rel
      (.inr (.inr q)) (fun _ : Fin 1 => y))
    (hFibre : y ∈
      (((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode).collapseDomain).func
          p.symbol (root ∘ p.argMap)) :
    (splitMaskJointRootReduct C).rel
      (hybridSplitOutputSymbol (splitMaskInputAtPart p q))
      (Structure.funcTuple root y) := by
  classical
  let Base : RelStructure (L.splitMaskHybrid Parts) V :=
    splitMaskJointRootReduct C
  let Old : RelStructure (L.wholeMaskPatternLanguage Parts) V :=
    splitMaskHybridOriginalOldReduct Base
  let xs : Fin (L.funcArity p.symbol) → V := root ∘ p.argMap
  have hyDecoded :
      y ∈ ((Old.wholeMaskPartialDecode).func p.symbol xs).getD ∅ := by
    exact hFibre
  cases hDecoded : (Old.wholeMaskPartialDecode).func p.symbol xs with
  | none =>
      have hEmpty : y ∈ (∅ : Set V) := by
        simpa only [hDecoded, Option.getD_none] using hyDecoded
      exact (Set.not_mem_empty y hEmpty).elim
  | some U =>
      have hyU : y ∈ U := by
        simpa only [hDecoded, Option.getD_some] using hyDecoded
      have hHas : HasWholeMaskValue Old p.symbol xs U :=
        (hNorm.normal.coherent.oldDecoder_func_some_iff
          hNorm.normal.positive
          hNorm.normal.injectiveDomains
          hNorm.normal.originalMasks hSplitTransport
          p.symbol xs U).mp hDecoded
      obtain ⟨m, r, hr, mask, t, hOld, hArgs, hSet⟩ := hHas
      let pat : FunctionInputPattern L := ⟨p.symbol, m, r, hr⟩
      let rootA : Fin m → V :=
        fun i => t (Fin.castAdd mask.size i)
      have hOldTuple :
          Base.rel (hybridOriginalMaskOutputSymbol pat mask) t :=
        hOld
      have hyRange :
          y ∈ Set.range
            (fun j : Fin mask.size => t (Fin.natAdd m j)) := by
        rw [← hSet]
        exact hyU
      obtain ⟨j, hj⟩ := hyRange
      have hUnaryJ :
          Base.rel (.inr (.inr (mask.label j)))
            (fun _ : Fin 1 => y) := by
        have hLabel :
            Base.rel (.inr (.inr (mask.label j)))
              (fun _ : Fin 1 => t (Fin.natAdd m j)) :=
          hNorm.normal.positive.2.2.2 pat mask j t hOldTuple
        simpa only [hj] using hLabel
      have hPartsUnique :
          HybridUniqueVertexPart Base :=
        hNorm.normal.coherent.1.2.2.2
      obtain ⟨q₀, hq₀, hUnique⟩ := hPartsUnique y
      have hJq₀ : mask.label j = q₀ :=
        hUnique (mask.label j) hUnaryJ
      have hQq₀ : q = q₀ := hUnique q hPart
      have hJq : mask.label j = q := hJq₀.trans hQq₀.symm
      let uA : Fin (m + 1) → V := Structure.funcTuple rootA y
      have hPrefixA (i : Fin m) :
          uA i.castSucc = t (Fin.castAdd mask.size i) :=
        Structure.funcTuple_castSucc rootA y i
      have hOutA :
          uA (Fin.last m) = t (Fin.natAdd m j) := by
        calc
          uA (Fin.last m) = y :=
            Structure.funcTuple_last rootA y
          _ = t (Fin.natAdd m j) := hj.symm
      have hSplitAJ :
          Base.rel
            (hybridSplitOutputSymbol
              (splitMaskInputAtPart pat (mask.label j))) uA :=
        (hNorm.normal.coherent.2 pat mask t j uA
          hOldTuple hPrefixA).mpr hOutA
      have hSplitAq :
          Base.rel
            (hybridSplitOutputSymbol
              (splitMaskInputAtPart pat q)) uA := by
        simpa only [hJq] using hSplitAJ
      have hSamePrimitive :
          rootA ∘ r = root ∘ p.argMap := by
        funext i
        exact (hArgs i).symm
      exact hSplitTransport p.symbol m p.rootSize
        r p.argMap hr p.onto
        rootA root q y hRootInj
        hSamePrimitive hSplitAq

end StructuralRamsey.RelStructure
