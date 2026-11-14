import AllThoseRamseyClasses.Published.TrackEHybridCrossPatternWholeFibre
import AllThoseRamseyClasses.Published.TrackEHybridOldDomainCoherence
import PartiteConstruction.Functional.WholeMaskPartialDecode2019

/-!
# Track E2: faithful old whole-value decoder from exact hybrid coherence

The verified OLD Option(Set) decoder `wholeMaskPartialDecode` chooses
one complete-value witness when the original OLD relational reduct
has a witness, but consistency of that choice is conditional:
arbitrary OLD structures can display two incompatible values of F(xs).

The new cross-PATTERN complete-output theorem proves exactly the
missing consistency condition for the ORIGINAL OLD reduct of the
actual hybrid relational Picture. Every pair of `HasWholeMaskValue`
witnesses of the same primitive (F,xs) must have equal WHOLE sets
of output vertices, regardless of which distinct-input equality
pattern or complete output mask was chosen.

As a consequence, the OLD whole-mask decoder is faithful on EACH
defined input in the precise sense of `func_some_iff`: it gives
`some U` exactly for real displayed complete OLD witnesses of U.
Unlike a source-defined partial map, no arbitrary witness choice
survives in the final proposition.

This does NOT yet identify OLD definedness with every active OLD
domain mask in an arbitrary noncanonical target; that needs the
independent joint-U-closed complete-output existence proof. It does
not prove that zero-width masks are excluded or that the full
finite-family E2 sparse Ramsey construction remains in this class.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Any TWO complete ORIGINAL OLD value witnesses of the same
primitive input F(xs) in a hybrid Picture satisfying all
cross-pattern coherence conditions carry the SAME actual set of
output vertices. The two witnesses may use distinct injective
input patterns and arbitrarily permuted output masks. -/
theorem HybridExactWeakCoherent.oldDecoder_uniqueValue
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridExactWeakCoherent E)
    (hSound : HybridPositiveOutputSound E)
    (hInjective : HybridActiveDomainRootInjective E)
    (hMasks : HybridOldMaskPatternTransport E)
    (hSplit : HybridSplitOutputPatternTransport E)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V)
    (U T : Set V)
    (hU : HasWholeMaskValue (splitMaskHybridOriginalOldReduct E)
      F xs U)
    (hT : HasWholeMaskValue (splitMaskHybridOriginalOldReduct E)
      F xs T) :
    U = T := by
  obtain ⟨m, r, hr, maskA, tA, hOldA, hArgsA, hUA⟩ := hU
  obtain ⟨n, s, hs, maskB, tB, hOldB, hArgsB, hTB⟩ := hT
  have hPosA :
      E.rel (hybridOriginalMaskOutputSymbol
        (⟨F, m, r, hr⟩ : FunctionInputPattern L) maskA) tA :=
    hOldA
  have hPosB :
      E.rel (hybridOriginalMaskOutputSymbol
        (⟨F, n, s, hs⟩ : FunctionInputPattern L) maskB) tB :=
    hOldB
  have hSameArgs :
      (fun i : Fin m => tA (Fin.castAdd maskA.size i)) ∘ r =
      (fun i : Fin n => tB (Fin.castAdd maskB.size i)) ∘ s := by
    funext i
    exact (hArgsA i).symm.trans (hArgsB i)
  have hFibre :
      Set.range (fun j : Fin maskA.size =>
        tA (Fin.natAdd m j)) =
      Set.range (fun k : Fin maskB.size =>
        tB (Fin.natAdd n k)) :=
    h.crossPattern_wholeOutputFibre_eq
      hSound hInjective hMasks hSplit
      F m n r s hr hs maskA maskB tA tB
      hPosA hPosB hSameArgs
  exact hUA.trans (hFibre.trans hTB.symm)

/-- The standard OLD whole-mask decoder recovers exactly every
displayed complete ORIGINAL value, without depending on a choice
of input equality-pattern presentation or complete output mask.
This is a FULL proof of unique VALUE interpretation, not of total
domain-record interpretation. -/
theorem HybridExactWeakCoherent.oldDecoder_func_some_iff
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridExactWeakCoherent E)
    (hSound : HybridPositiveOutputSound E)
    (hInjective : HybridActiveDomainRootInjective E)
    (hMasks : HybridOldMaskPatternTransport E)
    (hSplit : HybridSplitOutputPatternTransport E)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V)
    (U : Set V) :
    ((splitMaskHybridOriginalOldReduct E).wholeMaskPartialDecode).func
      F xs = some U ↔
    HasWholeMaskValue (splitMaskHybridOriginalOldReduct E)
      F xs U := by
  exact (splitMaskHybridOriginalOldReduct E).wholeMaskPartialDecode_func_some_iff
    F xs
    (fun U T hU hT =>
      h.oldDecoder_uniqueValue hSound hInjective hMasks hSplit
        F xs U T hU hT)
    U

end StructuralRamsey.RelStructure
