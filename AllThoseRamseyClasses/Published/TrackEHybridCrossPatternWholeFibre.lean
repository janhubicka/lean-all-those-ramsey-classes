import AllThoseRamseyClasses.Published.TrackEHybridSplitOutputPatternTransport
import AllThoseRamseyClasses.Published.TrackEHybridCoherencePackage
import AllThoseRamseyClasses.Published.TrackEHybridPositiveOutputSound
import AllThoseRamseyClasses.Published.TrackEHybridActiveDomainRootInjective
import AllThoseRamseyClasses.Published.TrackEHybridSplitDomainPatternTransport

/-!
# Track E2: exact ORIGINAL complete output fibres across input patterns

Native F(xs) is independent of which injective equality-pattern
enumeration of its DISTINCT input vertices represents xs. Previous
formalization proves:
* OLD active mask sets transport across such enumerations;
* split active domains transport across them;
* positive split-output tuples transport the SAME output vertex.

The last point makes it possible to transfer ACTUAL complete
multivalued output values, not merely their output part sets.
Take two visible complete OLD tuples for one primitive function F
using possibly different surjective input argument patterns and
possibly different complete output masks. Positive soundness supplies
the corresponding OLD domain predicates, while injective-domain
normality makes both displayed input roots genuine. Cross-pattern
OLD mask coherence matches the output part sets. For each output
vertex of the first whole tuple, visible whole/split agreement
produces a split (F,q) positive tuple. Transport it to the SECOND
input pattern with exactly the same output vertex, and use the
second visible whole/split agreement to identify the unique
q-coordinate of the second complete tuple. Repeat symmetrically.

The theorem concludes literal equality of the two full SETS of
output vertices when their original primitive input tuples agree.
It uses only visible data and no U-closedness, no generated hull,
no new output vertices and no speculative target decoder.
A separate step is still needed to show every activated OLD domain
has its complete tuple in the actual noncanonical U-closed target
(the stacked #1168 result), and to assemble the whole decoder.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Transfer each displayed original output vertex to a second
equality-pattern presentation of the SAME primitive arguments.
Unlike the fixed-pattern proof, this uses SAME-VERTEX positive
split-output pattern transport, not just mask/domain coherence. -/
private theorem crossPattern_wholeOutputRange_subset
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (hAgree : HybridVisibleWholeSplitAgreement E)
    (hSplit : HybridSplitOutputPatternTransport E)
    (F : L.FuncSymbol) (m n : ℕ)
    (r : Fin (L.funcArity F) → Fin m)
    (s : Fin (L.funcArity F) → Fin n)
    (hr : Function.Surjective r)
    (hs : Function.Surjective s)
    (maskA maskB : CompleteOutputParts Parts)
    (tA : Fin (m + maskA.size) → V)
    (tB : Fin (n + maskB.size) → V)
    (hA : E.rel (hybridOriginalMaskOutputSymbol
      (⟨F, m, r, hr⟩ : FunctionInputPattern L) maskA) tA)
    (hB : E.rel (hybridOriginalMaskOutputSymbol
      (⟨F, n, s, hs⟩ : FunctionInputPattern L) maskB) tB)
    (hParts : Set.range maskA.label ⊆ Set.range maskB.label)
    (hInjB : Function.Injective
      (fun i : Fin n => tB (Fin.castAdd maskB.size i)))
    (hArgs :
      (fun i : Fin m => tA (Fin.castAdd maskA.size i)) ∘ r =
      (fun i : Fin n => tB (Fin.castAdd maskB.size i)) ∘ s) :
    Set.range (fun j : Fin maskA.size =>
      tA (Fin.natAdd m j)) ⊆
    Set.range (fun k : Fin maskB.size =>
      tB (Fin.natAdd n k)) := by
  intro y hy
  obtain ⟨j, rfl⟩ := hy
  obtain ⟨k, hk⟩ :=
    hParts (show maskA.label j ∈ Set.range maskA.label from ⟨j, rfl⟩)
  let rootA : Fin m → V := fun i => tA (Fin.castAdd maskA.size i)
  let rootB : Fin n → V := fun i => tB (Fin.castAdd maskB.size i)
  let out : V := tA (Fin.natAdd m j)
  let uA : Fin (m + 1) → V := Structure.funcTuple rootA out
  let uB : Fin (n + 1) → V := Structure.funcTuple rootB out
  have hPrefixA : ∀ i : Fin m,
      uA i.castSucc = tA (Fin.castAdd maskA.size i) := by
    intro i
    exact Structure.funcTuple_castSucc rootA out i
  have hSplitA :
      E.rel (hybridSplitOutputSymbol
        (splitMaskInputAtPart
          (⟨F, m, r, hr⟩ : FunctionInputPattern L)
          (maskA.label j))) uA :=
    (hAgree (⟨F, m, r, hr⟩ : FunctionInputPattern L)
      maskA tA j uA hA hPrefixA).mpr
      (Structure.funcTuple_last rootA out)
  have hSplitB :
      E.rel (hybridSplitOutputSymbol
        (splitMaskInputAtPart
          (⟨F, n, s, hs⟩ : FunctionInputPattern L)
          (maskA.label j))) uB :=
    hSplit F m n r s hr hs rootA rootB
      (maskA.label j) out hInjB hArgs hSplitA
  have hSplitAtK :
      E.rel (hybridSplitOutputSymbol
        (splitMaskInputAtPart
          (⟨F, n, s, hs⟩ : FunctionInputPattern L)
          (maskB.label k))) uB := by
    rw [hk]
    exact hSplitB
  have hPrefixB : ∀ i : Fin n,
      uB i.castSucc = tB (Fin.castAdd maskB.size i) := by
    intro i
    exact Structure.funcTuple_castSucc rootB out i
  have hValueB :
      uB (Fin.last n) = tB (Fin.natAdd n k) :=
    (hAgree (⟨F, n, s, hs⟩ : FunctionInputPattern L)
      maskB tB k uB hB hPrefixB).mp hSplitAtK
  refine ⟨k, ?_⟩
  calc
    tA (Fin.natAdd m j) = uB (Fin.last n) :=
      (Structure.funcTuple_last rootB out).symm
    _ = tB (Fin.natAdd n k) := hValueB

/-- Every pair of visible complete original OLD output tuples
representing the same primitive F-input tuple has exactly the
same set of ACTUAL output vertices, EVEN when their distinct
input equality-patterns and complete output masks differ.

The original positive output/domain soundness and input-root
injectivity establish that both roots and masks are valid.
The OLD mask transport identifies the set of output parts,
and positive split transport plus SAME-VERTEX whole/split
agreement identifies each original output vertex.
No native decoder and no generated hull are assumed. -/
theorem HybridExactWeakCoherent.crossPattern_wholeOutputFibre_eq
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridExactWeakCoherent E)
    (hSound : HybridPositiveOutputSound E)
    (hInjective : HybridActiveDomainRootInjective E)
    (hMasks : HybridOldMaskPatternTransport E)
    (hSplit : HybridSplitOutputPatternTransport E)
    (F : L.FuncSymbol) (m n : ℕ)
    (r : Fin (L.funcArity F) → Fin m)
    (s : Fin (L.funcArity F) → Fin n)
    (hr : Function.Surjective r)
    (hs : Function.Surjective s)
    (maskA maskB : CompleteOutputParts Parts)
    (tA : Fin (m + maskA.size) → V)
    (tB : Fin (n + maskB.size) → V)
    (hA : E.rel (hybridOriginalMaskOutputSymbol
      (⟨F, m, r, hr⟩ : FunctionInputPattern L) maskA) tA)
    (hB : E.rel (hybridOriginalMaskOutputSymbol
      (⟨F, n, s, hs⟩ : FunctionInputPattern L) maskB) tB)
    (hArgs :
      (fun i : Fin m => tA (Fin.castAdd maskA.size i)) ∘ r =
      (fun i : Fin n => tB (Fin.castAdd maskB.size i)) ∘ s) :
    Set.range (fun j : Fin maskA.size =>
      tA (Fin.natAdd m j)) =
    Set.range (fun k : Fin maskB.size =>
      tB (Fin.natAdd n k)) := by
  let patA : FunctionInputPattern L := ⟨F, m, r, hr⟩
  let patB : FunctionInputPattern L := ⟨F, n, s, hs⟩
  let rootA : Fin m → V := fun i => tA (Fin.castAdd maskA.size i)
  let rootB : Fin n → V := fun i => tB (Fin.castAdd maskB.size i)
  have hDomA :
      E.rel (hybridOriginalMaskDomainSymbol patA maskA) rootA :=
    hSound.1 patA maskA tA hA
  have hDomB :
      E.rel (hybridOriginalMaskDomainSymbol patB maskB) rootB :=
    hSound.1 patB maskB tB hB
  have hInjA : Function.Injective rootA :=
    hInjective.1 patA maskA rootA hDomA
  have hInjB : Function.Injective rootB :=
    hInjective.1 patB maskB rootB hDomB
  have hPartEq :
      Set.range maskA.label = Set.range maskB.label :=
    hMasks.maskPartSetsAgree h.1.1
      F m n r s hr hs rootA rootB maskA maskB
      hInjB hArgs hDomA hDomB
  apply Set.Subset.antisymm
  · exact crossPattern_wholeOutputRange_subset h.2 hSplit
      F m n r s hr hs maskA maskB tA tB hA hB
      hPartEq.subset hInjB hArgs
  · exact crossPattern_wholeOutputRange_subset h.2 hSplit
      F n m s r hs hr maskB maskA tB tA hB hA
      hPartEq.symm.subset hInjA hArgs.symm

end StructuralRamsey.RelStructure
