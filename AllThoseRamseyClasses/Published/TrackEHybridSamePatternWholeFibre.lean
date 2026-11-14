import AllThoseRamseyClasses.Published.TrackEHybridCoherencePackage
import AllThoseRamseyClasses.Published.TrackEHybridPositiveOutputSound
import PartiteConstruction.Structure.Relationalize

/-!
# Track E2: complete original output tuples under distinct masks have one fibre

The corrected hybrid encoding retains complete original multivalued
output tuples, whose mask symbols enumerate the output PARTS. A finite
native function application can have its part set listed in several
orders, producing different complete-mask relation symbols. One
cannot decode a unique native function fibre merely from a unique
tuple PER mask unless the displayed output sets agree ACROSS masks.

This module resolves the same equality-pattern case directly.
Visible whole/split agreement says every displayed whole-output
coordinate induces its per-part singleton split graph tuple.
Apply that same agreement to a second positive whole tuple on the
SAME input root: the singleton split tuple fixes its corresponding
output vertex. Original active-domain mask-set uniqueness ensures
that every part slot of the first tuple occurs in the second.

The result is equality of COMPLETE SETS of output vertices, not
just equality of output-PART sets, and requires no generated hull,
no output completion, no functional decoder and no extra vertices.

Different input equality-pattern presentations of the same primitive
argument tuple remain a separate cross-pattern step, as does the
two-pass sparse ordered Ramsey theorem.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- If every output part listed by mask A is also present in mask B,
and both complete original tuples have the identical displayed
input root, the visible whole/split law forces every original
output vertex in tuple A to occur literally in tuple B. -/
private theorem samePattern_wholeOutputRange_subset
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (hAgree : HybridVisibleWholeSplitAgreement E)
    (p : FunctionInputPattern L)
    (mA mB : CompleteOutputParts Parts)
    (tA : Fin (p.rootSize + mA.size) → V)
    (tB : Fin (p.rootSize + mB.size) → V)
    (hA : E.rel (hybridOriginalMaskOutputSymbol p mA) tA)
    (hB : E.rel (hybridOriginalMaskOutputSymbol p mB) tB)
    (hParts : Set.range mA.label ⊆ Set.range mB.label)
    (hRoot : ∀ i : Fin p.rootSize,
      tA (Fin.castAdd mA.size i) =
        tB (Fin.castAdd mB.size i)) :
    Set.range (fun j : Fin mA.size =>
      tA (Fin.natAdd p.rootSize j)) ⊆
    Set.range (fun k : Fin mB.size =>
      tB (Fin.natAdd p.rootSize k)) := by
  intro y hy
  obtain ⟨j, rfl⟩ := hy
  obtain ⟨k, hk⟩ := hParts (show mA.label j ∈ Set.range mA.label from ⟨j, rfl⟩)
  let input : Fin p.rootSize → V :=
    fun i => tA (Fin.castAdd mA.size i)
  let u : Fin (p.rootSize + 1) → V :=
    Structure.funcTuple input (tA (Fin.natAdd p.rootSize j))
  have hPrefixA : ∀ i : Fin p.rootSize,
      u i.castSucc = tA (Fin.castAdd mA.size i) := by
    intro i
    exact Structure.funcTuple_castSucc input _ i
  have hLast :
      u (Fin.last p.rootSize) =
        tA (Fin.natAdd p.rootSize j) :=
    Structure.funcTuple_last input _
  have hSplitA :
      E.rel (hybridSplitOutputSymbol
        (splitMaskInputAtPart p (mA.label j))) u :=
    (hAgree p mA tA j u hA hPrefixA).mpr hLast
  have hSplitB :
      E.rel (hybridSplitOutputSymbol
        (splitMaskInputAtPart p (mB.label k))) u := by
    rw [hk]
    exact hSplitA
  have hPrefixB : ∀ i : Fin p.rootSize,
      u i.castSucc = tB (Fin.castAdd mB.size i) := by
    intro i
    calc
      u i.castSucc = tA (Fin.castAdd mA.size i) :=
        hPrefixA i
      _ = tB (Fin.castAdd mB.size i) := hRoot i
  have hValueB :
      u (Fin.last p.rootSize) =
        tB (Fin.natAdd p.rootSize k) :=
    (hAgree p mB tB k u hB hPrefixB).mp hSplitB
  exact ⟨k, hLast.symm.trans hValueB⟩

/-- Two visible COMPLETE original OLD output tuples on the SAME
primitive equality-pattern input root represent EXACTLY the
SAME SET of output vertices, regardless of which permutation
or enumeration of the active output-PART mask is used.

Positive-output soundness produces both input-domain mask relations.
The OLD mask coherence law gives equal sets of output parts, and
the visible whole/split law matches each output VERTEX.
This is not merely equality of mask labels. -/
theorem HybridExactWeakCoherent.samePattern_wholeOutputFibre_eq
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridExactWeakCoherent E)
    (hSound : HybridPositiveOutputSound E)
    (p : FunctionInputPattern L)
    (mA mB : CompleteOutputParts Parts)
    (tA : Fin (p.rootSize + mA.size) → V)
    (tB : Fin (p.rootSize + mB.size) → V)
    (hA : E.rel (hybridOriginalMaskOutputSymbol p mA) tA)
    (hB : E.rel (hybridOriginalMaskOutputSymbol p mB) tB)
    (hRoot : ∀ i : Fin p.rootSize,
      tA (Fin.castAdd mA.size i) =
        tB (Fin.castAdd mB.size i)) :
    Set.range (fun j : Fin mA.size =>
      tA (Fin.natAdd p.rootSize j)) =
    Set.range (fun k : Fin mB.size =>
      tB (Fin.natAdd p.rootSize k)) := by
  have hDomA :
      E.rel (hybridOriginalMaskDomainSymbol p mA)
        (fun i : Fin p.rootSize =>
          tA (Fin.castAdd mA.size i)) :=
    hSound.1 p mA tA hA
  have hDomB :
      E.rel (hybridOriginalMaskDomainSymbol p mB)
        (fun i : Fin p.rootSize =>
          tB (Fin.castAdd mB.size i)) :=
    hSound.1 p mB tB hB
  have hRootEq :
      (fun i : Fin p.rootSize =>
        tA (Fin.castAdd mA.size i)) =
      (fun i : Fin p.rootSize =>
        tB (Fin.castAdd mB.size i)) :=
    funext hRoot
  have hDomBOnA :
      E.rel (hybridOriginalMaskDomainSymbol p mB)
        (fun i : Fin p.rootSize =>
          tA (Fin.castAdd mA.size i)) := by
    rw [hRootEq]
    exact hDomB
  have hParts :
      Set.range mA.label = Set.range mB.label :=
    h.1.1 p mA mB
      (fun i : Fin p.rootSize =>
        tA (Fin.castAdd mA.size i))
      hDomA hDomBOnA
  apply Set.Subset.antisymm
  · exact samePattern_wholeOutputRange_subset
      h.2 p mA mB tA tB hA hB hParts.subset hRoot
  · exact samePattern_wholeOutputRange_subset
      h.2 p mB mA tB tA hB hA hParts.symm.subset
      (fun i => (hRoot i).symm)

end StructuralRamsey.RelStructure
