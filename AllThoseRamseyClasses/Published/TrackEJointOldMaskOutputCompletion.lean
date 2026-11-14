import AllThoseRamseyClasses.Published.TrackEHybridNoDefinedEmptyMask
import AllThoseRamseyClasses.Published.TrackEJointHybridFullRootRules
import AllThoseRamseyClasses.Published.TrackEJointTagSemanticExact
import PartiteConstruction.Ramsey.ClosureDescription2019

/-!
# Track E2: exact original whole-output witnesses from a noncanonical joint-U-closed target

An arbitrary BASE hybrid Picture can activate an ORIGINAL complete
output-mask domain predicate without displaying any complete
function-output tuple, or with several incompatible complete tuples.
Those are genuine obstacles to decoding arbitrary relational Pictures
as partial/native set-valued function structures.

For an ACTUAL JOINT-TAGGED Picture C we show that these
failures cannot occur when the following facts all hold:
* C is U-CLOSED for the literal joint full-hybrid-root 2019 rules;
* the fresh root tags have EXACT semantics over its BASE reduct;
* an active ORIGINAL mask domain has an injective distinct-input root;
* its output mask has positive width (no defined-empty mask);
* its distinct-input root size is strictly positive.

The argument is constructive in Lean. Take the exact hybrid induced
root pattern on the displayed input tuple, use input-root injectivity
to embed the entire root, and activate the appropriate fresh
ORIGINAL full-hybrid-root closure rule. Literal U-closedness gives
ONE tagged output tuple. Exact tag semantics gives ONE complete
original old output tuple on exactly those input vertices.
Conversely any other positive complete tuple with that SAME
input root produces the SAME tag and is therefore equal by the
U-closure uniqueness clause.

This does NOT independently show that two distinct OUTPUT MASKS
on the same primitive input have identical values (the older
mask-set/label transport controls their parts but not every
cross-mask output tuple), nor supply a native decoder or the
finite-family ordered sparse Ramsey theorem.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- In an arbitrary ACTUAL noncanonical joint-tagged U-CLOSED
target with exact tag semantics, an active nonempty original
mask over an injective POSITIVE input root determines a
UNIQUE complete original output tuple, on the SAME input
vertices. No output vertex is adjoined and the ambient carrier
is unchanged. -/
theorem originalMask_hasUniqueFullOutput_of_jointUClosed
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hClosed : IsUClosed (L.splitMaskJointClosureRules Parts) C)
    (hExact : HasExactJointRootTags C)
    (hInjective : HybridActiveDomainRootInjective
      (splitMaskJointRootReduct C))
    (hNoEmpty : HybridNoDefinedEmptyOriginalMask
      (splitMaskJointRootReduct C))
    (p : FunctionInputPattern L)
    (mask : CompleteOutputParts Parts)
    (root : Fin p.rootSize → V)
    (hPositiveRoot : 0 < p.rootSize)
    (hOld : (splitMaskJointRootReduct C).rel
      (hybridOriginalMaskDomainSymbol p mask) root) :
    ∃! t : Fin (p.rootSize + mask.size) → V,
      (splitMaskJointRootReduct C).rel
        (hybridOriginalMaskOutputSymbol p mask) t ∧
      ∀ i : Fin p.rootSize,
        t (Fin.castAdd mask.size i) = root i := by
  classical
  let base : RelStructure (L.splitMaskHybrid Parts) V :=
    splitMaskJointRootReduct C
  have hInj : Function.Injective root :=
    hInjective.1 p mask root hOld
  let actualRoot :
      RelStructure (L.splitMaskHybrid Parts) (Fin p.rootSize) := {
    rel := fun R xs => base.rel R (root ∘ xs)
  }
  let eRoot : Embedding actualRoot base := {
    toFun := root
    injective := hInj
    map_rel_iff := by
      intro R xs
      rfl
  }
  have hRootDomain :
      actualRoot.rel (hybridOriginalMaskDomainSymbol p mask) id := by
    change base.rel (hybridOriginalMaskDomainSymbol p mask) (root ∘ id)
    have hid : root ∘ id = root := by
      funext i
      rfl
    exact
      (congrArg (fun xs : Fin p.rootSize → V =>
        base.rel (hybridOriginalMaskDomainSymbol p mask) xs) hid).symm.mp
        hOld
  let pattern : OriginalMaskHybridRootPattern L Parts := {
    input := p
    mask := mask
    rootPositive := hPositiveRoot
    outputPositive := hNoEmpty p mask root hOld
    root := actualRoot
    hasDomain := hRootDomain
  }
  have hRule : pattern.jointClosureRule ∈
      (L.splitMaskJointClosureRules Parts) :=
    Or.inr ⟨pattern, rfl⟩
  have hExactEq :
      C = splitMaskJointRootExpansion base := hExact
  have hUCanon :
      IsUClosed (L.splitMaskJointClosureRules Parts)
        (splitMaskJointRootExpansion base) := by
    rw [← hExactEq]
    exact hClosed
  obtain ⟨t, hValid, hUnique⟩ :=
    (hUCanon pattern.jointClosureRule hRule).2
      eRoot.splitMaskJointRoot
  have hOldTuple :
      base.rel (hybridOriginalMaskOutputSymbol p mask) t := by
    have hTagged :
        (splitMaskJointRootExpansion base).rel
          (.inr (.inr pattern)) t := hValid.1
    exact hTagged.1
  have hPrefix :
      ∀ i : Fin p.rootSize,
        t (Fin.castAdd mask.size i) = root i := by
    intro i
    exact hValid.2 i
  refine ⟨t, ⟨hOldTuple, hPrefix⟩, ?_⟩
  intro ys hYs
  have hTaggedYs :
      (splitMaskJointRootExpansion base).rel
        (.inr (.inr pattern)) ys := by
    change base.rel (hybridOriginalMaskOutputSymbol p mask) ys ∧
      ∃ g : Embedding actualRoot base,
        ∀ i : Fin p.rootSize,
          ys (Fin.castAdd mask.size i) = g i
    exact ⟨hYs.1, eRoot, hYs.2⟩
  exact hUnique ys ⟨hTaggedYs, hYs.2⟩

/-- The full no-defined-empty JOINT target-normality certificate
supplies precisely the injective-domain and positive-output-width
premises needed by the previous exact one-output theorem. This
works for arbitrary NONCANONICAL targets without postulating
their native function decoder. -/
theorem HybridJointNoEmptyNormal.originalMask_hasUniqueFullOutput
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hClosed : IsUClosed (L.splitMaskJointClosureRules Parts) C)
    (p : FunctionInputPattern L)
    (mask : CompleteOutputParts Parts)
    (root : Fin p.rootSize → V)
    (hPositiveRoot : 0 < p.rootSize)
    (hOld : (splitMaskJointRootReduct C).rel
      (hybridOriginalMaskDomainSymbol p mask) root) :
    ∃! t : Fin (p.rootSize + mask.size) → V,
      (splitMaskJointRootReduct C).rel
        (hybridOriginalMaskOutputSymbol p mask) t ∧
      ∀ i : Fin p.rootSize,
        t (Fin.castAdd mask.size i) = root i :=
  originalMask_hasUniqueFullOutput_of_jointUClosed
    hClosed hNorm.normal.exactTags
    hNorm.normal.injectiveDomains hNorm.noEmpty
    p mask root hPositiveRoot hOld

end StructuralRamsey.RelStructure
