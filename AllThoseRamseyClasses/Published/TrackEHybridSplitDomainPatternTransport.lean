import AllThoseRamseyClasses.Published.TrackEHybridOldMaskPatternFree
import AllThoseRamseyClasses.Published.TrackEHybridMaskSplitDomainCompatibility

/-!
# Track E2: split input domains are invariant under exact equality-pattern presentation

An original native input tuple may have many injective distinct-root
presentations when its primitive coordinates repeat. In a correct
hybrid relational picture, neither the original complete output-PART
mask nor the corresponding per-part split input domain can depend
on which enumeration of the same distinct input vertices is used.

The previous ORIGINAL-mask cross-pattern transport, same-pattern
mask-set coherence, split-domain mask coverage and mask/split
compatibility imply the two precise conclusions below:
* original masks on two presentations of the same primitive input
  have identical SETS of output parts;
* a split part-domain active on one presentation is active on every
  other injective presentation of that exact input tuple.

The second implication is a genuine target-side decoder consistency
test, including repeated input coordinates and nullary primitive
functions. It is stable on literal weak cuts without inventing
output vertices. The hypotheses are individually free-amalgam
stable by earlier checked results, but we do not duplicate their
amalgamation proofs here.

Neither statement asserts existence of an output value, mixed
U-closed profile compatibility, arbitrary target decoding, or the
finite-family E2 Ramsey witness.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Two activated original masks attached to possibly DIFFERENT
injective presentations of the SAME primitive argument tuple
must describe exactly the same output-PART SET. Their enumerations
may differ. -/
theorem HybridOldMaskPatternTransport.maskPartSetsAgree
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (hTransport : HybridOldMaskPatternTransport E)
    (hCoherent : SplitMaskHybridOriginalDomainCoherent E)
    (F : L.FuncSymbol) (m n : ℕ)
    (r : Fin (L.funcArity F) → Fin m)
    (s : Fin (L.funcArity F) → Fin n)
    (hr : Function.Surjective r)
    (hs : Function.Surjective s)
    (rootA : Fin m → V) (rootB : Fin n → V)
    (maskA maskB : CompleteOutputParts Parts)
    (hInjB : Function.Injective rootB)
    (hArgs : rootA ∘ r = rootB ∘ s)
    (hMaskA : E.rel (hybridOriginalMaskDomainSymbol
      (⟨F, m, r, hr⟩ : FunctionInputPattern L) maskA) rootA)
    (hMaskB : E.rel (hybridOriginalMaskDomainSymbol
      (⟨F, n, s, hs⟩ : FunctionInputPattern L) maskB) rootB) :
    Set.range maskA.label = Set.range maskB.label := by
  have hAonB : E.rel (hybridOriginalMaskDomainSymbol
      (⟨F, n, s, hs⟩ : FunctionInputPattern L) maskA) rootB :=
    hTransport F m n r s hr hs rootA rootB maskA
      hInjB hArgs hMaskA
  exact hCoherent (⟨F, n, s, hs⟩ : FunctionInputPattern L)
    maskA maskB rootB hAonB hMaskB

/-- Exact cross-pattern transport for the singleton (F, q)
SPLIT input domain. The alternative injective root lists
the same primitive input tuple in a possibly different order. -/
def HybridSplitDomainPatternTransport
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  ∀ (F : L.FuncSymbol) (m n : ℕ)
    (r : Fin (L.funcArity F) → Fin m)
    (s : Fin (L.funcArity F) → Fin n)
    (hr : Function.Surjective r)
    (hs : Function.Surjective s)
    (rootA : Fin m → V)
    (rootB : Fin n → V)
    (q : Parts),
    Function.Injective rootB →
    rootA ∘ r = rootB ∘ s →
    E.rel (hybridSplitDomainSymbol
      (splitMaskInputAtPart
        (⟨F, m, r, hr⟩ : FunctionInputPattern L) q)) rootA →
    E.rel (hybridSplitDomainSymbol
      (splitMaskInputAtPart
        (⟨F, n, s, hs⟩ : FunctionInputPattern L) q)) rootB

/-- ORIGINAL mask transport plus exact split-domain mask coverage
and mask/split compatibility force the split input-domain to be
independent of the chosen equality-pattern presentation.

Use the EXISTING original mask on the first presentation, move
that SAME mask to the second via cross-pattern transport, then
read off the specified split part q. -/
theorem HybridSplitDomainPatternTransport.ofMaskLaws
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (hTransport : HybridOldMaskPatternTransport E)
    (hCovered : HybridSplitDomainMaskCovered E)
    (hCompatible : HybridMaskSplitDomainCompatible E) :
    HybridSplitDomainPatternTransport E := by
  intro F m n r s hr hs rootA rootB q hInjB hArgs hSplitA
  obtain ⟨mask, hMaskA, hq⟩ :=
    hCovered (⟨F, m, r, hr⟩ : FunctionInputPattern L)
      q rootA hSplitA
  have hMaskB : E.rel (hybridOriginalMaskDomainSymbol
      (⟨F, n, s, hs⟩ : FunctionInputPattern L) mask) rootB :=
    hTransport F m n r s hr hs rootA rootB mask
      hInjB hArgs hMaskA
  exact (hCompatible
    (⟨F, n, s, hs⟩ : FunctionInputPattern L)
    mask q rootB hMaskB).2 hq

/-- In a finite genuine native partite system, the entire
per-part split input-domain family is independent of the
injective enumeration of the original repeated input tuple. -/
theorem canonicalHybrid_splitDomainPatternTransport
    {V : Type w} [Finite V]
    (A : FunctionalPartite.System L Parts V) :
    HybridSplitDomainPatternTransport A.splitMaskHybrid :=
  HybridSplitDomainPatternTransport.ofMaskLaws
    (canonicalHybrid_oldMaskPatternTransport A)
    (canonicalHybrid_splitDomainMaskCovered A)
    (canonicalHybrid_maskSplitDomainCompatible A)

/-- Literal exact weak restriction preserves split-domain
cross-pattern transport even when the complete output tuple
is not visible after restriction. -/
theorem HybridSplitDomainPatternTransport.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridSplitDomainPatternTransport E)
    (S : Set V) :
    HybridSplitDomainPatternTransport (E.induce S) := by
  intro F m n r s hr hs rootA rootB q hInjB hArgs hSplitA
  have hInjBV : Function.Injective (Subtype.val ∘ rootB) := by
    intro i j hij
    apply hInjB
    exact Subtype.ext hij
  have hArgsV :
      (Subtype.val ∘ rootA) ∘ r =
        (Subtype.val ∘ rootB) ∘ s := by
    funext i
    exact congrArg Subtype.val (congrFun hArgs i)
  exact h F m n r s hr hs
    (Subtype.val ∘ rootA) (Subtype.val ∘ rootB)
    q hInjBV hArgsV hSplitA

end StructuralRamsey.RelStructure
