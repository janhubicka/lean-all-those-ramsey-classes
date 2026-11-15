import AllThoseRamseyClasses.Published.TrackEJointNormalTargetClass
import PartiteConstruction.Iterated.LocalTreeLike

/-!
# Track E2: exclude spurious defined-empty ORIGINAL output masks

The complete-output-parts language intentionally permits the
ZERO-width mask. For an arbitrary partial Option(Set) function it
correctly represents a DEFINED-EMPTY value. But an actual NATIVE
set-valued Structure is encoded by toNonemptyPartial: an EMPTY native
fibre is represented by UNDEFINED (none), not defined-empty.

The previously merged HybridJointTargetNormal class controls
cross-pattern masks, singleton split domains, positive outputs,
unary parts and the exact full-root tags. It does not by itself
assert that a positive ORIGINAL OLD mask domain has a nonempty
output mask. This is a separate necessary target-decoding guard.

We name and prove the NO-DEFINED-EMPTY invariant: every activated
ORIGINAL complete mask has a POSITIVE output width. Any genuinely
native canonical partite System satisfies it. It is preserved by
literal exact weak induction (domain predicates are not recomputed)
and by true FULL base-hybrid relational free amalgamation (each
positive mask-domain tuple comes from one side).

Combining it with the previously merged target-normality predicate
gives a separate STRICT normality package, source-valid and stable
on exact weak restrictions and on TRUE FULL joint free amalgams over
relatively joint-U-closed seams. This package is a necessary
condition for native decoding, not a proof that arbitrary weak
Pictures have all output witnesses or a functional decoder.

No part of the frozen manuscript is changed and no output vertices
or closure hulls are introduced.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- No active ORIGINAL OLD mask-domain tuple can claim a
DEFINED-EMPTY value. In canonical toNonemptyPartial sources the
native fibre is defined iff it is nonempty, whereas the whole
mask language itself also admits width-zero symbols. -/
def HybridNoDefinedEmptyOriginalMask
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  ∀ (p : FunctionInputPattern L)
    (mask : CompleteOutputParts Parts)
    (root : Fin p.rootSize → V),
    E.rel (hybridOriginalMaskDomainSymbol p mask) root →
    0 < mask.size

/-- Every genuinely native partite source has NO activated
zero-width complete ORIGINAL mask: a positive old mask domain
records an actually nonempty native function fibre, and hence
at least one output-part coordinate. -/
theorem canonicalHybrid_noDefinedEmptyOriginalMask
    {V : Type w}
    (A : FunctionalPartite.System L Parts V) :
    HybridNoDefinedEmptyOriginalMask A.splitMaskHybrid := by
  classical
  intro p mask root hOld
  have hVal :
      ∃ U : Set V,
        A.toStructure.toNonemptyPartial.func p.symbol
          (root ∘ p.argMap) = some U ∧
        A.part '' U = Set.range mask.label := by
    exact hOld.2
  obtain ⟨U, hDefined, hParts⟩ := hVal
  have hNativeNonempty :
      (A.func p.symbol (root ∘ p.argMap)).Nonempty := by
    by_contra hn
    have hNone :
        A.toStructure.toNonemptyPartial.func p.symbol
          (root ∘ p.argMap) = none := by
      change (if (A.func p.symbol (root ∘ p.argMap)).Nonempty
        then some (A.func p.symbol (root ∘ p.argMap))
        else none) = none
      simp [hn]
    rw [hNone] at hDefined
    cases hDefined
  have hUEq : A.func p.symbol (root ∘ p.argMap) = U := by
    change (if (A.func p.symbol (root ∘ p.argMap)).Nonempty
      then some (A.func p.symbol (root ∘ p.argMap))
      else none) = some U at hDefined
    simpa only [if_pos hNativeNonempty, Option.some.injEq] using
      hDefined
  obtain ⟨y, hy⟩ := hNativeNonempty
  have hyU : y ∈ U := by
    rw [← hUEq]
    exact hy
  have hOutputPart : A.part y ∈ Set.range mask.label := by
    rw [← hParts]
    exact ⟨y, hyU, rfl⟩
  obtain ⟨j, _⟩ := hOutputPart
  have hNe : mask.size ≠ 0 := by
    intro hz
    have k : Fin 0 := hz ▸ j
    exact k.elim0
  exact Nat.pos_of_ne_zero hNe

/-- EXACT weak induction retains any activated old mask domain
but cannot turn its strictly positive mask width into zero.
This remains true even when all displayed output vertices
escape the weak test and the old output tuple disappears. -/
theorem HybridNoDefinedEmptyOriginalMask.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridNoDefinedEmptyOriginalMask E) (S : Set V) :
    HybridNoDefinedEmptyOriginalMask (E.induce S) := by
  intro p mask root hMask
  exact h p mask (Subtype.val ∘ root) hMask

/-- NO-DEFINED-EMPTY old mask domains are stable under every
true FULL base-hybrid relational free amalgam of matching
source-side structures. A positive OLD mask relation cannot
arise as a mixed tuple. -/
theorem HybridNoDefinedEmptyOriginalMask.freeAmalgam
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hLeft : HybridNoDefinedEmptyOriginalMask Left)
    (hRight : HybridNoDefinedEmptyOriginalMask Right) :
    HybridNoDefinedEmptyOriginalMask Whole := by
  intro p mask root hMask
  rcases (hFree.rel_iff (hybridOriginalMaskDomainSymbol p mask) root).mp
      hMask with
    ⟨x, hx, _⟩ | ⟨y, hy, _⟩
  · exact hLeft p mask x hx
  · exact hRight p mask y hy

/-- The strengthened ACTUAL joint-tagged normality condition
records separately that the originally native full-fibre
encoding has no spurious defined-empty OLD mask domain. -/
structure HybridJointNoEmptyNormal
    {V : Type w}
    (C : RelStructure (L.splitMaskJointRootLanguage Parts) V) : Prop where
  normal : HybridJointTargetNormal C
  noEmpty : HybridNoDefinedEmptyOriginalMask (splitMaskJointRootReduct C)

/-- Every finite genuine native partite System belongs to the
strengthened joint target class on literally its own vertices. -/
theorem canonicalHybrid_jointNoEmptyNormal
    {V : Type w} [Finite V]
    (A : FunctionalPartite.System L Parts V) :
    HybridJointNoEmptyNormal
      (splitMaskJointRootExpansion A.splitMaskHybrid) :=
  ⟨canonicalHybrid_jointTargetNormal A,
    canonicalHybrid_noDefinedEmptyOriginalMask A⟩

/-- The STRICT normality package survives EVERY exact weak cut,
without requiring function closure of the chosen vertex set. -/
theorem HybridJointNoEmptyNormal.induce
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (h : HybridJointNoEmptyNormal C) (S : Set V) :
    HybridJointNoEmptyNormal (C.induce S) :=
  ⟨h.normal.induce S, h.noEmpty.induce S⟩

/-- The strengthened joint normality property survives a true
FULL relational free amalgam provided the actual joint-U-closed
root images force the same-output-vertex coherence. This does
NOT claim any such amalgam exists for arbitrary weak roots. -/
theorem HybridJointNoEmptyNormal.freeAmalgam_of_jointClosedSeams
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskJointRootLanguage Parts) H}
    {Left : RelStructure (L.splitMaskJointRootLanguage Parts) E}
    {Right : RelStructure (L.splitMaskJointRootLanguage Parts) F}
    {Whole : RelStructure (L.splitMaskJointRootLanguage Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hPositive :
      ∀ p : FunctionInputPattern (L.outputPartIndexed Parts),
        0 < p.rootSize)
    (hRoot : HybridJointNoEmptyNormal Root)
    (hLeft : HybridJointNoEmptyNormal Left)
    (hRight : HybridJointNoEmptyNormal Right)
    (hClosedLeft :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        Left (Set.range sL))
    (hClosedRight :
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        Right (Set.range sR)) :
    HybridJointNoEmptyNormal Whole := by
  constructor
  · exact HybridJointTargetNormal.freeAmalgam_of_jointClosedSeams
      hFree hPositive hRoot.normal hLeft.normal hRight.normal
      hClosedLeft hClosedRight
  · exact HybridNoDefinedEmptyOriginalMask.freeAmalgam
      hFree.splitMaskJointRootReduct
      hLeft.noEmpty hRight.noEmpty

end StructuralRamsey.RelStructure
