import AllThoseRamseyClasses.Published.TrackEJointOldMaskOutputCompletion
import AllThoseRamseyClasses.Published.TrackEHybridOldDecoderUnique
import AllThoseRamseyClasses.Published.TrackEJointClosedNormalStrongAmalgam
import PartiteConstruction.Structure.Relationalize

/-!
# Track E2: every visible split output is a genuine decoded native output

A strengthened normal, joint-U-closed hybrid target carries both
per-part singleton split output incidences and complete ORIGINAL OLD
mask output tuples. A visible singleton split output could appear
spurious if it were not contained in any complete OLD output fibre.

This module proves the necessary ORIGINAL-completeness implication
without creating new vertices. Positive split output soundness
produces an active split domain; split-domain mask coverage supplies
an ORIGINAL OLD mask containing the output part. Literal joint
U-closedness and the exact full-root tag semantics then supply
a complete original output tuple for the SAME input root, and the
visible same-vertex whole/split law identifies the singleton
output with the designated complete-output coordinate.

With the now certified cross-pattern value-uniqueness theorem, the
existing ORIGINAL OLD decoder chooses this complete output set.
Consequently the positive split vertex is a member of the actual
native `collapseDomain` fibre on the SAME original primitive input.

This is the forward (soundness) half of split-output/native-graph
correspondence in the noncanonical final tagged target. It is not
the converse: to re-encode all positive split relations, one also
needs to transfer native whole-output witnesses across input
equality patterns and verify the full canonical tagged languages.
No new vertex, hull, alternate decoder or two-pass sparse ordered
Ramsey witness is asserted.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- A positive (F,q) split incidence in an ACTUAL strict-normal
JOINT U-closed target has an ORIGINAL complete OLD output tuple
on the identical displayed input root, and its output vertex is
literally the q-coordinate of that complete tuple.

The witness is already present in the target; no completion
vertex or output-hull is introduced. -/
theorem HybridJointNoEmptyNormal.splitOutput_hasCompleteOldWitness
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hClosed : IsUClosed (L.splitMaskJointClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (p : FunctionInputPattern L) (q : Parts)
    (u : Fin (p.rootSize + 1) → V)
    (hSplit : (splitMaskJointRootReduct C).rel
      (hybridSplitOutputSymbol (splitMaskInputAtPart p q)) u) :
    ∃ (mask : CompleteOutputParts Parts)
      (t : Fin (p.rootSize + mask.size) → V)
      (j : Fin mask.size),
      (splitMaskJointRootReduct C).rel
        (hybridOriginalMaskOutputSymbol p mask) t ∧
      (∀ i : Fin p.rootSize,
        u i.castSucc = t (Fin.castAdd mask.size i)) ∧
      mask.label j = q ∧
      u (Fin.last p.rootSize) =
        t (Fin.natAdd p.rootSize j) := by
  classical
  let Base : RelStructure (L.splitMaskHybrid Parts) V :=
    splitMaskJointRootReduct C
  let root : Fin p.rootSize → V := fun i => u i.castSucc
  have hDomain :
      Base.rel (hybridSplitDomainSymbol
        (splitMaskInputAtPart p q)) root :=
    hNorm.normal.positive.2.1
      (splitMaskInputAtPart p q) u hSplit
  obtain ⟨mask, hMask, ⟨j, hj⟩⟩ :=
    hNorm.normal.coherent.1.2.2.1
      p q root hDomain
  have hRootPositive : 0 < p.rootSize := by
    simpa [splitMaskInputAtPart] using
      (hPos.splitPatternRootPositive (splitMaskInputAtPart p q))
  obtain ⟨t, ⟨hWhole, hRoot⟩, _⟩ :=
    hNorm.originalMask_hasUniqueFullOutput
      hClosed p mask root hRootPositive hMask
  have hPrefix (i : Fin p.rootSize) :
      u i.castSucc = t (Fin.castAdd mask.size i) :=
    (hRoot i).symm
  have hSplitAtPart :
      Base.rel (hybridSplitOutputSymbol
        (splitMaskInputAtPart p (mask.label j))) u := by
    rw [hj]
    exact hSplit
  have hOutput :
      u (Fin.last p.rootSize) =
        t (Fin.natAdd p.rootSize j) :=
    (hNorm.normal.coherent.2 p mask t j u
      hWhole hPrefix).mp hSplitAtPart
  exact ⟨mask, t, j, hWhole, hPrefix, hj, hOutput⟩

/-- Every visible positive singleton split-incidence vertex is
already a value of the ORIGINAL native function obtained from
the existing OLD complete-mask decoder on the SAME target carrier.

Unlike a merely part-preserving homomorphism, this is an actual
membership statement in the decoded native set-valued fibre,
on the exact ORIGINAL primitive input tuple. -/
theorem HybridJointNoEmptyNormal.splitOutput_mem_oldDecodedNative
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hClosed : IsUClosed (L.splitMaskJointClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hSplitTransport : HybridSplitOutputPatternTransport
      (splitMaskJointRootReduct C))
    (p : FunctionInputPattern L) (q : Parts)
    (u : Fin (p.rootSize + 1) → V)
    (hSplit : (splitMaskJointRootReduct C).rel
      (hybridSplitOutputSymbol (splitMaskInputAtPart p q)) u) :
    u (Fin.last p.rootSize) ∈
      (((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode).collapseDomain).func
        p.symbol
        ((fun i : Fin p.rootSize => u i.castSucc) ∘ p.argMap) := by
  classical
  let Base : RelStructure (L.splitMaskHybrid Parts) V :=
    splitMaskJointRootReduct C
  let Old : RelStructure (L.wholeMaskPatternLanguage Parts) V :=
    splitMaskHybridOriginalOldReduct Base
  let xs : Fin (L.funcArity p.symbol) → V :=
    (fun i : Fin p.rootSize => u i.castSucc) ∘ p.argMap
  obtain ⟨mask, t, j, hWhole, hRoot, _, hOutput⟩ :=
    hNorm.splitOutput_hasCompleteOldWitness
      hClosed hPos p q u hSplit
  let U : Set V := Set.range (fun k : Fin mask.size =>
    t (Fin.natAdd p.rootSize k))
  have hHas : HasWholeMaskValue Old p.symbol xs U := by
    refine ⟨p.rootSize, p.argMap, p.onto,
      mask, t, ?_, ?_, rfl⟩
    · exact hWhole
    · intro i
      exact hRoot (p.argMap i)
  have hSome :
      (Old.wholeMaskPartialDecode).func p.symbol xs = some U :=
    (hNorm.normal.coherent.oldDecoder_func_some_iff
      hNorm.normal.positive hNorm.normal.injectiveDomains
      hNorm.normal.originalMasks hSplitTransport
      p.symbol xs U).mpr hHas
  have hMember : u (Fin.last p.rootSize) ∈ U :=
    ⟨j, hOutput.symm⟩
  change ((Old.wholeMaskPartialDecode).func p.symbol xs).getD ∅
      |>.IsMember (u (Fin.last p.rootSize))
  simpa only [hSome, Option.getD_some] using hMember

end StructuralRamsey.RelStructure
