import AllThoseRamseyClasses.Published.TrackEHybridSplitDomainDecoderIff
import AllThoseRamseyClasses.Published.TrackEHybridSplitNativeGraphIff
import AllThoseRamseyClasses.Published.TrackEHybridPrimitiveRelationCopyCoherence
import AllThoseRamseyClasses.Published.TrackESplitPatternOriginalInputEquiv
import AllThoseRamseyClasses.Published.TrackEHybridNativePartiteSystem
import PartiteConstruction.Structure.Relationalize

/-!
# Track E2: the entire singleton split OLD pattern graph is native

The exact hybrid presentation carries a split component with:
* one copy of every ORIGINAL primitive relational symbol;
* an active split (F,q) input-domain relation for EVERY
  surjective primitive input equality pattern;
* the positive singleton split (F,q) output-incidence relation
  on the same distinct input root and its displayed vertex.

The already merged native decoder normality yields a genuine
partite System on the SAME original carrier. Three independent
pieces are necessary to compare its canonical singleton split
OLD graph with the ACTUAL noncanonical hybrid split component:
1. original/split PRIMITIVE relation copies agree;
2. active split DOMAIN symbols reflect exactly existence of
   a decoded native output in the specified part;
3. positive split OUTPUT tuples agree with literal membership
   of the same vertex in that decoded native fibre.

The latter two results are formulated for ORIGINAL equality
patterns `FunctionInputPattern L`, while the whole split OLD
language ranges over ALL patterns in
`FunctionInputPattern (L.outputPartIndexed Parts)`.
The exact inverse split pattern index from the preceding
Track E2 module discharges this enumeration mismatch without
discarding repeated primitive input positions or nullaries.

This module first extracts the literal split OLD pattern-graph
reduct of ANY base hybrid Picture and then proves that in an
ACTUAL strict-normal, joint-U-CLOSED target with positive
primitive function arities, complete-mask domain saturation and
primitive-copy synchronization, that OLD reduct is **EXACTLY**
the canonical `A.splitOutputParts.toStructure.patternGraph`
of the reconstructed native System A on the SAME carrier.
It uses no new vertices, generated hull, independent decoder
or extra function witnesses.

This is the base split patternGraph equality, NOT yet the
nested split tag or outer joint-tag equality, nor the
two-pass finite-family ordered E2 Ramsey witness.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Retain the ACTUAL singleton split OLD equality-pattern
graph relations from the hybrid base structure, forgetting
both its nested pattern tags and its original complete masks.
No tuple is recomputed by this reduct. -/
def hybridSplitPatternGraphReduct
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) :
    RelStructure ((L.outputPartIndexed Parts).patternGraph) V where
  rel R t := E.rel (.inr (.inl (.inl R))) t

/-- All split OLD graph data in an actual U-closed native-partite
normal JOINT target agrees with the canonical singleton split
pattern graph of the EXISTING reconstructed native System.

The extra ORIGINAL mask saturation is used in the exact split
domain law; the independently maintained original/split
primitive relation copy equivalence is needed to match the
relational component. The positive output case uses EXACT
same-vertex positive split/native membership, including the
actual unary part label and injective distinct-input roots.
-/
theorem HybridJointNativePartiteClosed.splitPatternGraphReduct_eq_native
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (h : HybridJointNativePartiteClosed C)
    (hPos : L.PositiveFuncArity)
    (hSaturated : HybridOriginalMaskDomainSaturated
      (splitMaskJointRootReduct C))
    (hCopies : HybridPrimitiveRelationCopiesAgree
      (splitMaskJointRootReduct C)) :
    hybridSplitPatternGraphReduct (splitMaskJointRootReduct C) =
      (h.2.toNativeSystem.splitOutputParts.toStructure).patternGraph := by
  classical
  let Base : RelStructure (L.splitMaskHybrid Parts) V :=
    splitMaskJointRootReduct C
  let A : FunctionalPartite.System L Parts V :=
    h.2.toNativeSystem
  let partNormal : HybridUniqueVertexPart Base :=
    h.2.strict.normal.coherent.1.2.2.2
  apply RelStructure.rel_injective
  funext R t
  apply propext
  rcases R with R | R
  · have hSame := hCopies.rel_iff R.down t
    have hNative := h.2.nativeSystem_rel_iff R.down t
    exact hSame.symm.trans hNative.symm
  · rcases R with p | p
    · let pOrig : FunctionInputPattern L :=
        splitMaskOriginalInput p
      let q : Parts := p.symbol.2
      have hPattern :
          splitMaskInputAtPart pOrig q = p :=
        splitMaskInputAtPart_original_eq p
      have hDomain :=
        h.2.strict.splitDomain_iff_oldDecodedPart
          h.1 hPos h.2.splitOutput hSaturated pOrig q t
      have hDomainSymbol :
          hybridSplitDomainSymbol (splitMaskInputAtPart pOrig q) =
            hybridSplitDomainSymbol p :=
        congrArg hybridSplitDomainSymbol hPattern
      have hDomain' :
          Base.rel (hybridSplitDomainSymbol p) t ↔
            Function.Injective t ∧
            ∃ y : V,
              y ∈ A.func p.symbol.1.down (t ∘ p.argMap) ∧
              A.part y = q := by
        simpa only [hDomainSymbol] using hDomain
      exact hDomain'
    · let pOrig : FunctionInputPattern L :=
        splitMaskOriginalInput p
      let q : Parts := p.symbol.2
      let root : Fin p.rootSize → V :=
        fun i => t i.castSucc
      let y : V := t (Fin.last p.rootSize)
      have hPattern :
          splitMaskInputAtPart pOrig q = p :=
        splitMaskInputAtPart_original_eq p
      have hTuple : Structure.funcTuple root y = t := by
        change Structure.funcTuple
          (fun i : Fin p.rootSize => t i.castSucc)
          (t (Fin.last p.rootSize)) = t
        exact Structure.funcTuple_eta t
      change Base.rel (hybridSplitOutputSymbol p) t ↔
        Function.Injective root ∧
          y ∈ (A.splitOutputParts.toStructure).func p.symbol
            (root ∘ p.argMap)
      constructor
      · intro hOutput
        have hDomain :
            Base.rel (hybridSplitDomainSymbol p) root :=
          h.2.strict.normal.positive.2.1 p t hOutput
        have hInj : Function.Injective root :=
          h.2.strict.normal.injectiveDomains.2 p root hDomain
        have hLabel :
            Base.rel (.inr (.inr q))
              (fun _ : Fin 1 => y) :=
          h.2.strict.normal.positive.2.2.1 p t hOutput
        have hOriginalPositive :
            Base.rel
              (hybridSplitOutputSymbol
                (splitMaskInputAtPart pOrig q))
              (Structure.funcTuple root y) := by
          rw [hPattern, hTuple]
          exact hOutput
        have hNative :
            y ∈ A.func p.symbol.1.down
              (root ∘ p.argMap) :=
          (h.2.strict.splitOutput_iff_oldDecodedNative_mem
            h.1 hPos h.2.splitOutput pOrig root hInj
            q y hLabel).mp hOriginalPositive
        have hPart : A.part y = q :=
          partNormal.partMap_eq_of_label y q hLabel
        exact ⟨hInj, ⟨hNative, hPart⟩⟩
      · rintro ⟨hInj, hy⟩
        have hNative :
            y ∈ A.func p.symbol.1.down
              (root ∘ p.argMap) := hy.1
        have hPart : A.part y = q := hy.2
        have hLabel :
            Base.rel (.inr (.inr q))
              (fun _ : Fin 1 => y) := by
          have hq := partNormal.partMap_hasLabel y
          rw [hPart] at hq
          exact hq
        have hOriginalPositive :
            Base.rel
              (hybridSplitOutputSymbol
                (splitMaskInputAtPart pOrig q))
              (Structure.funcTuple root y) :=
          (h.2.strict.splitOutput_iff_oldDecodedNative_mem
            h.1 hPos h.2.splitOutput pOrig root hInj
            q y hLabel).mpr hNative
        rw [hPattern, hTuple] at hOriginalPositive
        exact hOriginalPositive

end StructuralRamsey.RelStructure
