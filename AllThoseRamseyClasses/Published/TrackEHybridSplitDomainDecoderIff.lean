import AllThoseRamseyClasses.Published.TrackEHybridOldMaskDomainDecoderIff
import AllThoseRamseyClasses.Published.TrackEHybridMaskSplitDomainCompatibility
import AllThoseRamseyClasses.Published.TrackEHybridOldDecoderUnique

/-!
# Track E2: exact SPLIT domain predicates of the old native decoder

The canonical singleton-by-output-part split function (F,q) is
DEFINED precisely when the original native multivalued function
F(xs) has at least one output vertex in part q. The hybrid
relational language stores this as a separate positive input
DOMAIN predicate, even on exact weak tests that forget some
outputs. Arbitrary noncanonical Pictures can contain phantom
split domains not witnessed by a native positive value.

The merged exact mask/split-domain compatibility laws connect
each split domain to an active complete ORIGINAL output-part
mask; the old-mask decoder equivalence (#1233) interprets that
mask as a genuine nonempty decoded value with exactly that set
of output PARTS. Thus every active split domain has a native
output of its designated part.

Conversely, a decoded OLD native fibre vertex y with part q
comes from a REAL complete original output tuple. Its active
original mask transports to the requested input equality
pattern, and mask/split compatibility forces the corresponding
split domain. This direction needs neither U-closedness nor
a positive primitive arity once the native member is visible.

The result identifies the exact split input-domain relation
with the per-part positive nonempty value predicate of the
EXISTING native OLD decoder on the same original carrier.
It is a necessary re-encoding step, not a claim that arbitrary
weak nonclosed Pictures are U-closed or that the two-pass sparse
ordered Ramsey construction preserves this normal class.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Every actual positive split input-domain predicate of a
strict-normal joint-U-closed target is EXACTLY an injective
distinct-input root whose ORIGINAL decoded native function
has an output in the specified unary part q.

The native output vertex is not invented: the OLD complete
mask supplied by the split-domain coverage law has an
already present complete value via the joint closure rules.
The converse uses a displayed OLD whole tuple and old-mask
cross-pattern transport, rather than assuming a split graph
value in advance. -/
theorem HybridJointNoEmptyNormal.splitDomain_iff_oldDecodedPart
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hClosed : IsUClosed (L.splitMaskJointClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hSplitTransport : HybridSplitOutputPatternTransport
      (splitMaskJointRootReduct C))
    (hSaturated : HybridOriginalMaskDomainSaturated
      (splitMaskJointRootReduct C))
    (p : FunctionInputPattern L)
    (q : Parts)
    (root : Fin p.rootSize → V) :
    (splitMaskJointRootReduct C).rel
      (hybridSplitDomainSymbol (splitMaskInputAtPart p q)) root ↔
    Function.Injective root ∧
      ∃ y : V,
        y ∈
          (((splitMaskHybridOriginalOldReduct
            (splitMaskJointRootReduct C)).wholeMaskPartialDecode).collapseDomain).func
            p.symbol (root ∘ p.argMap) ∧
        hNorm.normal.coherent.1.2.2.2.partMap y = q := by
  classical
  let Base : RelStructure (L.splitMaskHybrid Parts) V :=
    splitMaskJointRootReduct C
  let Old : RelStructure (L.wholeMaskPatternLanguage Parts) V :=
    splitMaskHybridOriginalOldReduct Base
  let part : V → Parts :=
    hNorm.normal.coherent.1.2.2.2.partMap
  let xs : Fin (L.funcArity p.symbol) → V := root ∘ p.argMap
  constructor
  · intro hSplitDomain
    obtain ⟨mask, hMask, hq⟩ :=
      hNorm.normal.coherent.1.2.2.1
        p q root hSplitDomain
    obtain ⟨hInj, U, hSome, hPartSet⟩ :=
      (hNorm.originalMaskDomain_iff_oldDecoded
        hClosed hPos hSplitTransport hSaturated
        p mask root).mp hMask
    have hPartMem : q ∈ part '' U := by
      rw [hPartSet]
      exact hq
    obtain ⟨y, hyU, hyq⟩ := hPartMem
    have hyNative :
        y ∈ ((Old.wholeMaskPartialDecode).collapseDomain).func
          p.symbol xs := by
      change y ∈ ((Old.wholeMaskPartialDecode).func p.symbol xs).getD ∅
      simpa only [hSome, Option.getD_some] using hyU
    exact ⟨hInj, y, hyNative, hyq⟩
  · rintro ⟨hInj, y, hyNative, hyPart⟩
    have hyDecoder :
        y ∈ ((Old.wholeMaskPartialDecode).func p.symbol xs).getD ∅ :=
      hyNative
    cases hSome : (Old.wholeMaskPartialDecode).func p.symbol xs with
    | none =>
        have hImpossible : y ∈ (∅ : Set V) := by
          simpa only [hSome, Option.getD_none] using hyDecoder
        simp at hImpossible
    | some U =>
        have hyU : y ∈ U := by
          simpa only [hSome, Option.getD_some] using hyDecoder
        have hHas : HasWholeMaskValue Old p.symbol xs U :=
          (hNorm.normal.coherent.oldDecoder_func_some_iff
            hNorm.normal.positive hNorm.normal.injectiveDomains
            hNorm.normal.originalMasks hSplitTransport
            p.symbol xs U).mp hSome
        obtain ⟨m, r, hr, mask, t, hOutput, hArgs, hU⟩ := hHas
        let patB : FunctionInputPattern L :=
          ⟨p.symbol, m, r, hr⟩
        let rootB : Fin m → V :=
          fun i => t (Fin.castAdd mask.size i)
        have hPositive :
            Base.rel (hybridOriginalMaskOutputSymbol patB mask) t :=
          hOutput
        have hDomainB :
            Base.rel (hybridOriginalMaskDomainSymbol patB mask) rootB :=
          hNorm.normal.positive.1 patB mask t hPositive
        have hArgsEq : rootB ∘ r = root ∘ p.argMap := by
          funext i
          exact (hArgs i).symm
        have hDomainOnRoot :
            Base.rel (hybridOriginalMaskDomainSymbol p mask) root :=
          hNorm.normal.originalMasks
            p.symbol m p.rootSize r p.argMap hr p.onto
            rootB root mask hInj hArgsEq hDomainB
        have hyRange :
            y ∈ Set.range
              (fun j : Fin mask.size => t (Fin.natAdd m j)) := by
          rw [← hU]
          exact hyU
        obtain ⟨j, hj⟩ := hyRange
        have hPartJ :
            part (t (Fin.natAdd m j)) = mask.label j :=
          hNorm.normal.coherent.1.2.2.2.partMap_eq_of_label
            (t (Fin.natAdd m j)) (mask.label j)
            (hNorm.normal.positive.2.2.2 patB mask j t hPositive)
        have hq : q ∈ Set.range mask.label := by
          refine ⟨j, ?_⟩
          calc
            mask.label j = part (t (Fin.natAdd m j)) :=
              (hPartJ).symm
            _ = part y := congrArg part hj
            _ = q := hyPart
        exact (hNorm.normal.coherent.1.2.1 p mask q root
          hDomainOnRoot).2 hq

end StructuralRamsey.RelStructure
