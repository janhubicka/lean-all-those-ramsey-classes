import AllThoseRamseyClasses.Published.TrackEHybridOldMaskPatternTransport
import PartiteConstruction.Iterated.LocalTreeLike

/-!
# Track E2: cross-pattern ORIGINAL output-mask transport is free-amalgamation stable

The ORIGINAL complete-mask input-root encoding is not unique:
surjective argument maps can enumerate the same distinct primitive
input vertices in different orders. The exact domain mask attached
to an original native function application must be independent of
this equality-pattern choice.

The previous module proves the law on canonical native sources and
literal exact weak cuts. This module proves that the SAME law is
preserved by every TRUE FULL relational free amalgam of base
hybrid Pictures whose TWO sides already satisfy it.

If one complete mask domain tuple lies on the left, its primitive
input arguments are in the left. The alternative root enumerates
only vertices appearing in this SAME primitive argument tuple:
the other surjective argument pattern allows us to select a
source-side preimage of EACH alternative root coordinate. Since
the corresponding whole alternative root is injective, this
side root is also injective. The left side's cross-pattern
transport law gives the SAME original mask at that alternative
root, which the full left embedding transports back into the
whole free amalgam. The right case is symmetric.

No common-root lookup oracle, new output vertices, generated
closure hull or independent function completion is used.
The primitive function input arity may be zero; surjectivity
ensures the appropriate empty-root case.

This is one more target-side domain normality law preserved under
exact weak induction AND free attachments. It does not prove
arbitrary hybrid output-fibre decoding, mixed U-closed profile
compatibility, or the finite-family ordered E2 Ramsey theorem.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- One local side transport argument: if an ORIGINAL full mask on
the first exact primitive input root comes from a FULL embedded
side, then EVERY other injective root enumeration of that SAME
primitive input is contained in that side as well, because its
surjective argument pattern lists every root vertex.

The SAME original mask relation therefore transports to the whole
on the alternative root. No native decoder is involved. -/
private theorem oldMaskPatternTransport_fromSide
    {X Y : Type w}
    {Side : RelStructure (L.splitMaskHybrid Parts) X}
    {Whole : RelStructure (L.splitMaskHybrid Parts) Y}
    (e : Embedding Side Whole)
    (hSide : HybridOldMaskPatternTransport Side)
    (F : L.FuncSymbol) (m n : ℕ)
    (r : Fin (L.funcArity F) → Fin m)
    (s : Fin (L.funcArity F) → Fin n)
    (hr : Function.Surjective r)
    (hs : Function.Surjective s)
    (rootA : Fin m → Y)
    (rootB : Fin n → Y)
    (mask : CompleteOutputParts Parts)
    (x : Fin m → X)
    (hSideMask :
      Side.rel (hybridOriginalMaskDomainSymbol
        (⟨F, m, r, hr⟩ : FunctionInputPattern L) mask) x)
    (hFirstRoot : rootA = e ∘ x)
    (hInjB : Function.Injective rootB)
    (hArgs : rootA ∘ r = rootB ∘ s) :
    Whole.rel (hybridOriginalMaskDomainSymbol
      (⟨F, n, s, hs⟩ : FunctionInputPattern L) mask) rootB := by
  classical
  let sideB : Fin n → X :=
    fun j => x (r (Classical.choose (hs j)))
  have hB : rootB = e ∘ sideB := by
    funext j
    calc
      rootB j =
          rootB (s (Classical.choose (hs j))) :=
        (congrArg rootB (Classical.choose_spec (hs j))).symm
      _ = rootA (r (Classical.choose (hs j))) :=
        (congrFun hArgs (Classical.choose (hs j))).symm
      _ = e (x (r (Classical.choose (hs j)))) :=
        congrFun hFirstRoot (r (Classical.choose (hs j)))
      _ = e (sideB j) := rfl
  have hSideBInj : Function.Injective sideB := by
    intro i j hij
    apply hInjB
    calc
      rootB i = e (sideB i) := congrFun hB i
      _ = e (sideB j) := congrArg e hij
      _ = rootB j := (congrFun hB j).symm
  have hSideArgs : x ∘ r = sideB ∘ s := by
    funext i
    apply e.injective
    calc
      e (x (r i)) = rootA (r i) :=
        (congrFun hFirstRoot (r i)).symm
      _ = rootB (s i) := congrFun hArgs i
      _ = e (sideB (s i)) := congrFun hB (s i)
  have hSideTarget :
      Side.rel (hybridOriginalMaskDomainSymbol
        (⟨F, n, s, hs⟩ : FunctionInputPattern L) mask) sideB :=
    hSide F m n r s hr hs x sideB mask
      hSideBInj hSideArgs hSideMask
  have hWholeTarget :
      Whole.rel (hybridOriginalMaskDomainSymbol
        (⟨F, n, s, hs⟩ : FunctionInputPattern L) mask)
        (e ∘ sideB) :=
    (e.map_rel_iff
      (hybridOriginalMaskDomainSymbol
        (⟨F, n, s, hs⟩ : FunctionInputPattern L) mask)
      sideB).mpr hSideTarget
  rw [hB]
  exact hWholeTarget

/-- CROSS-PATTERN OLD mask-domain transport is stable under true
FULL base-hybrid relational free amalgamation, assuming the two
sides already satisfy the transport property. No common-root
transport hypothesis is separately necessary.

Every positive OLD mask tuple localizes to one side, and both
surjective input patterns list exactly the same primitive input
vertices, so the alternative injective root stays on that side. -/
theorem HybridOldMaskPatternTransport.freeAmalgam
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hLeft : HybridOldMaskPatternTransport Left)
    (hRight : HybridOldMaskPatternTransport Right) :
    HybridOldMaskPatternTransport Whole := by
  intro F m n r s hr hs rootA rootB mask hInjB hArgs hOld
  rcases (hFree.rel_iff
      (hybridOriginalMaskDomainSymbol
        (⟨F, m, r, hr⟩ : FunctionInputPattern L) mask)
      rootA).mp hOld with
    ⟨x, hx, hFirst⟩ | ⟨x, hx, hFirst⟩
  · exact oldMaskPatternTransport_fromSide iL hLeft
      F m n r s hr hs rootA rootB mask x hx
      hFirst hInjB hArgs
  · exact oldMaskPatternTransport_fromSide iR hRight
      F m n r s hr hs rootA rootB mask x hx
      hFirst hInjB hArgs

end StructuralRamsey.RelStructure
