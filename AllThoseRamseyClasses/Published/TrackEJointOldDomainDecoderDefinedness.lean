import AllThoseRamseyClasses.Published.TrackEJointOldMaskOutputCompletion
import AllThoseRamseyClasses.Published.TrackEHybridOldDomainCoherence
import PartiteConstruction.Functional.WholeMaskPartialDecode2019

/-!
# Track E2: OLD native decoder definedness exactly matches active OLD domains

The already merged OLD complete-mask `wholeMaskPartialDecode` is
defined at primitive F(xs) iff at least one complete OLD output
tuple exists. In a general weak relational Picture, an active
OLD domain mask can survive while its output tuple is absent,
and the two conditions need not agree.

In an ACTUAL JOINT U-CLOSED target with exact root-tag semantics,
active-root injectivity, no zero-width original masks, and
positive primitive function arity, the checked Track E2
complete-output theorem (#1168) supplies one complete OLD
output tuple for EVERY active OLD mask domain. Conversely,
positive-output soundness sends every complete OLD tuple
back to its active OLD domain mask.

Thus on precisely the original vertex carrier and without a
generated hull, the existing partial decoder has its independent
definedness bit exactly where the ORIGINAL OLD hybrid Picture
has an active mask-domain predicate. This equivalence does not
need cross-mask VALUE uniqueness, and therefore can be formalized
independently of the pending cross-pattern fibre proof.

This theorem does not assert that arbitrary weak induced tests
are U-closed, that the decoded values are unique across different
input masks, or the finite-family ordered E2 Ramsey witness.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- On any exact U-closed strict-normal JOINT tagged target,
every active ORIGINAL OLD domain mask gives a displayed complete
OLD output tuple, and each displayed complete output tuple
entails its active ORIGINAL OLD domain mask.

The primitive positive-arity hypothesis guarantees the required
positive DISTINCT input-root size. The zero-width output-mask
obstruction is excluded by the separate strict-normality guard. -/
theorem HybridJointNoEmptyNormal.oldDomain_iff_hasWholeValue
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hClosed : IsUClosed (L.splitMaskJointClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V) :
    HasWholeMaskDomain
      (splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)) F xs ↔
    ∃ U : Set V,
      HasWholeMaskValue
        (splitMaskHybridOriginalOldReduct
          (splitMaskJointRootReduct C)) F xs U := by
  let Base : RelStructure (L.splitMaskHybrid Parts) V :=
    splitMaskJointRootReduct C
  let Old : RelStructure (L.wholeMaskPatternLanguage Parts) V :=
    splitMaskHybridOriginalOldReduct Base
  constructor
  · rintro ⟨m, r, hr, mask, root, hMask, hArgs⟩
    let p : FunctionInputPattern L := ⟨F, m, r, hr⟩
    have hOld : Base.rel (hybridOriginalMaskDomainSymbol p mask) root :=
      hMask
    have hNonzero : m ≠ 0 := by
      intro hm
      have k : Fin 0 := hm ▸ r (⟨0, hPos F⟩ : Fin (L.funcArity F))
      exact k.elim0
    have hPositiveRoot : 0 < m := Nat.pos_of_ne_zero hNonzero
    obtain ⟨t, ⟨hTuple, hRoot⟩, _⟩ :=
      hNorm.originalMask_hasUniqueFullOutput
        hClosed p mask root hPositiveRoot hOld
    refine ⟨Set.range (fun j : Fin mask.size =>
        t (Fin.natAdd m j)),
      m, r, hr, mask, t, ?_, ?_, rfl⟩
    · exact hTuple
    · intro i
      exact (hArgs i).trans (hRoot (r i)).symm
  · rintro ⟨U, m, r, hr, mask, t, hTuple, hArgs, hValue⟩
    let p : FunctionInputPattern L := ⟨F, m, r, hr⟩
    have hOutput :
        Base.rel (hybridOriginalMaskOutputSymbol p mask) t :=
      hTuple
    have hDomain :
        Base.rel (hybridOriginalMaskDomainSymbol p mask)
          (fun i : Fin m => t (Fin.castAdd mask.size i)) :=
      hNorm.normal.positive.1 p mask t hOutput
    exact ⟨m, r, hr, mask,
      (fun i : Fin m => t (Fin.castAdd mask.size i)),
      hDomain, hArgs⟩

/-- The existing OLD whole-mask partial decoder has its function
value UNDEFINED precisely when the genuine original hybrid OLD
domain relation is inactive. No separate decoded domain oracle
is added and no vertex is inserted.

Value uniqueness across all complete output presentations is a
separate theorem; the present conclusion only concerns the
Option(Set) definedness bit. -/
theorem HybridJointNoEmptyNormal.oldDecoder_none_iff_noDomain
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hClosed : IsUClosed (L.splitMaskJointClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V) :
    ((splitMaskHybridOriginalOldReduct
      (splitMaskJointRootReduct C)).wholeMaskPartialDecode).func
        F xs = none ↔
    ¬ HasWholeMaskDomain
      (splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)) F xs := by
  let Old : RelStructure (L.wholeMaskPatternLanguage Parts) V :=
    splitMaskHybridOriginalOldReduct (splitMaskJointRootReduct C)
  have hDomain :
      HasWholeMaskDomain Old F xs ↔
        ∃ U : Set V, HasWholeMaskValue Old F xs U :=
    hNorm.oldDomain_iff_hasWholeValue hClosed hPos F xs
  have hNone :
      (Old.wholeMaskPartialDecode).func F xs = none ↔
        ¬ ∃ U : Set V, HasWholeMaskValue Old F xs U :=
    Old.wholeMaskPartialDecode_func_none_iff F xs
  constructor
  · intro hn hd
    exact (hNone.mp hn) (hDomain.mp hd)
  · intro hd
    apply hNone.mpr
    intro hv
    exact hd (hDomain.mpr hv)

end StructuralRamsey.RelStructure
