import AllThoseRamseyClasses.Published.TrackEJointHybridExactInduce
import PartiteConstruction.Functional.OutputPartSingletonization
import PartiteConstruction.Functional.WholeMaskClosureSemiClosed2019
import PartiteConstruction.Functional.PartialSetFunctionsPartPredicates2019

/-!
# Track E2: canonical JOINT full-hybrid-root tags are U-closed

The canonical hybrid representation of an actual native functional
partite System has two complementary kinds of positive function data:
per-output-part singleton incidences and original complete
multivalued output-part masks. The joint closure description contains
FRESH tags for each of these over their FULL induced hybrid root.

The two U-closedness proofs share the same full-root embedding:
* split: the active root-domain relation gives a real (F,q) output,
  and singleton-valuedness forces one tagged output tuple;
* original mask: the active original root-domain relation gives an
  actual defined output set U with exact part image q. Use the
  required transversality to choose exactly one source output for
  each named part, producing the full old output tuple. The
  verified wholeMaskPatternGraph_unique_outputs theorem proves
  uniqueness of any two such tuples over the same full root.

This does not enlarge weak source carriers or replace ambient
domain bits by weakly recomputed ones. Original primitive input
tuples with repeated coordinates are represented by their exact
distinct-input equality patterns. Nullary-input and defined-empty
Option(Set) cases still require separate root treatment.

The result is canonical SOURCE U-closedness for the entire JOINT
closure description, not arbitrary noncanonical picture decoding,
hybrid strong/free amalgamation, or the E2 sparse Ramsey theorem.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Language

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Every genuine native transversal System has a U-closed
canonical JOINT split/mask hybrid expansion, using the literal
2019 full positive-root closure description of #1066.
Both closure families are checked, with no closure hull. -/
theorem System.splitMaskJointRoot_isUClosed
    (A : System L Parts V) :
    IsUClosed (L.splitMaskJointClosureRules Parts)
      (splitMaskJointRootExpansion A.splitMaskHybrid) := by
  classical
  intro rule hrule
  rcases hrule with hSplit | hMask
  · obtain ⟨p, rfl⟩ := hSplit
    constructor
    · intro t ht
      change A.splitMaskHybrid.rel
          (hybridSplitOutputSymbol p.input) t ∧
          ∃ e : RelStructure.Embedding p.root A.splitMaskHybrid,
            ∀ i : Fin p.input.rootSize, t i.castSucc = e i at ht
      obtain ⟨_, e, he⟩ := ht
      exact ⟨e.splitMaskJointRoot, he⟩
    · intro e
      let old : RelStructure.Embedding p.root A.splitMaskHybrid :=
        e.splitMaskJointRootReduct
      let root : Fin p.input.rootSize → V := fun i => old i
      have hDomain :
          A.splitMaskHybrid.rel (hybridSplitDomainSymbol p.input)
            (old ∘ id) :=
        (old.map_rel_iff (hybridSplitDomainSymbol p.input) id).mpr
          p.hasDomain
      have hSplitDomain :
          Function.Injective root ∧
          ((A.splitOutputParts).toStructure.func
            p.input.symbol (root ∘ p.input.argMap)).Nonempty := by
        change Function.Injective root ∧
          ((A.splitOutputParts).toStructure.func
            p.input.symbol (root ∘ p.input.argMap)).Nonempty at hDomain
        exact hDomain
      obtain ⟨hInj, y, hy⟩ := hSplitDomain
      let t : Fin (p.input.rootSize + 1) → V :=
        Structure.funcTuple root y
      have hGraph : A.splitMaskHybrid.rel
          (hybridSplitOutputSymbol p.input) t := by
        change Function.Injective
            (fun i : Fin p.input.rootSize => t i.castSucc) ∧
          t (Fin.last p.input.rootSize) ∈
            (A.splitOutputParts).toStructure.func p.input.symbol
              ((fun i : Fin p.input.rootSize => t i.castSucc) ∘
                p.input.argMap)
        simpa only [t, Structure.funcTuple_castSucc,
          Structure.funcTuple_last] using
          (show Function.Injective root ∧
            y ∈ (A.splitOutputParts).toStructure.func
              p.input.symbol (root ∘ p.input.argMap)
            from ⟨hInj, hy⟩)
      have hTag :
          (splitMaskJointRootExpansion A.splitMaskHybrid).rel
            (.inr (.inl p)) t := by
        change A.splitMaskHybrid.rel
          (hybridSplitOutputSymbol p.input) t ∧
          ∃ g : RelStructure.Embedding p.root A.splitMaskHybrid,
            ∀ i : Fin p.input.rootSize, t i.castSucc = g i
        exact ⟨hGraph, old, fun i => Structure.funcTuple_castSucc root y i⟩
      have hPrefix : ∀ i : Fin p.input.rootSize,
          t i.castSucc = e i := by
        intro i
        change t i.castSucc = root i
        exact Structure.funcTuple_castSucc root y i
      refine ⟨t, ⟨hTag, hPrefix⟩, ?_⟩
      intro ys hValid
      have hPrefixY : ∀ i : Fin p.input.rootSize,
          ys i.castSucc = root i := hValid.2
      have hY : ys (Fin.last p.input.rootSize) ∈
          (A.splitOutputParts).toStructure.func
            p.input.symbol (root ∘ p.input.argMap) := by
        have hOld : A.splitMaskHybrid.rel
            (hybridSplitOutputSymbol p.input) ys := hValid.1.1
        change Function.Injective
            (fun i : Fin p.input.rootSize => ys i.castSucc) ∧
          ys (Fin.last p.input.rootSize) ∈
            (A.splitOutputParts).toStructure.func p.input.symbol
              ((fun i : Fin p.input.rootSize => ys i.castSucc) ∘
                p.input.argMap) at hOld
        have hEq : (fun i : Fin p.input.rootSize => ys i.castSucc) =
            root := funext hPrefixY
        rw [hEq] at hOld
        exact hOld.2
      have hLast : ys (Fin.last p.input.rootSize) = y :=
        A.splitOutputParts_singletonValued
          p.input.symbol (root ∘ p.input.argMap) _ _ hY hy
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [t, Structure.funcTuple_last] using hLast
      · simpa only [t, Structure.funcTuple_castSucc] using hPrefixY j
  · obtain ⟨p, rfl⟩ := hMask
    constructor
    · intro t ht
      change A.splitMaskHybrid.rel
          (hybridOriginalMaskOutputSymbol p.input p.mask) t ∧
          ∃ e : RelStructure.Embedding p.root A.splitMaskHybrid,
            ∀ i : Fin p.input.rootSize,
              t (Fin.castAdd p.mask.size i) = e i at ht
      obtain ⟨_, e, he⟩ := ht
      exact ⟨e.splitMaskJointRoot, he⟩
    · intro e
      let old : RelStructure.Embedding p.root A.splitMaskHybrid :=
        e.splitMaskJointRootReduct
      let root : Fin p.input.rootSize → V := fun i => old i
      have hDomain :
          A.splitMaskHybrid.rel
            (hybridOriginalMaskDomainSymbol p.input p.mask)
            (old ∘ id) :=
        (old.map_rel_iff
          (hybridOriginalMaskDomainSymbol p.input p.mask) id).mpr
          p.hasDomain
      have hValue :
          Function.Injective root ∧
          ∃ U : Set V,
            A.toStructure.toNonemptyPartial.func
              p.input.symbol (root ∘ p.input.argMap) = some U ∧
            A.part '' U = Set.range p.mask.label := by
        change Function.Injective root ∧
          ∃ U : Set V,
            A.toStructure.toNonemptyPartial.func
              p.input.symbol (root ∘ p.input.argMap) = some U ∧
            A.part '' U = Set.range p.mask.label at hDomain
        exact hDomain
      obtain ⟨hInj, U, hFuncU, hMaskEq⟩ := hValue
      have hTransNative :
          FibreTransversal A.toStructure.toNonemptyPartial A.part :=
        (nativeFunctionFibreTransversal_iff_partial
          A.toStructure A.part).mp A.funcTransversal
      have hPartWitness (j : Fin p.mask.size) :
          ∃ y : V, y ∈ U ∧ A.part y = p.mask.label j := by
        have hLabel : p.mask.label j ∈ Set.range p.mask.label :=
          ⟨j, rfl⟩
        rw [← hMaskEq] at hLabel
        exact hLabel
      let out : Fin p.mask.size → V :=
        fun j => Classical.choose (hPartWitness j)
      have hOutMem (j : Fin p.mask.size) : out j ∈ U :=
        (Classical.choose_spec (hPartWitness j)).1
      have hOutPart (j : Fin p.mask.size) :
          A.part (out j) = p.mask.label j :=
        (Classical.choose_spec (hPartWitness j)).2
      have hRange : Set.range out = U := by
        ext y
        constructor
        · rintro ⟨j, rfl⟩
          exact hOutMem j
        · intro hy
          have hPart : A.part y ∈ Set.range p.mask.label := by
            rw [← hMaskEq]
            exact ⟨y, hy, rfl⟩
          obtain ⟨j, hj⟩ := hPart
          have hEq : out j = y :=
            hTransNative p.input.symbol (root ∘ p.input.argMap)
              U hFuncU (out j) (hOutMem j) y hy
              ((hOutPart j).trans hj)
          exact ⟨j, hEq⟩
      let t : Fin (p.input.rootSize + p.mask.size) → V :=
        Fin.append root out
      have hGraph :
          (A.toStructure.toNonemptyPartial.wholeMaskPatternGraph
            A.part).rel (.inr (.inr (p.input, p.mask))) t := by
        change Function.Injective
            (fun i : Fin p.input.rootSize =>
              t (Fin.castAdd p.mask.size i)) ∧
          A.toStructure.toNonemptyPartial.func
            p.input.symbol
              ((fun i : Fin p.input.rootSize =>
                t (Fin.castAdd p.mask.size i)) ∘ p.input.argMap) =
                some (Set.range (fun j : Fin p.mask.size =>
                  t (Fin.natAdd p.input.rootSize j))) ∧
          (∀ j : Fin p.mask.size,
            A.part (t (Fin.natAdd p.input.rootSize j)) = p.mask.label j)
        simp only [t, Fin.append_left, Fin.append_right]
        refine ⟨hInj, ?_, hOutPart⟩
        rw [hRange]
        exact hFuncU
      have hTag :
          (splitMaskJointRootExpansion A.splitMaskHybrid).rel
            (.inr (.inr p)) t := by
        change A.splitMaskHybrid.rel
          (hybridOriginalMaskOutputSymbol p.input p.mask) t ∧
            ∃ g : RelStructure.Embedding p.root A.splitMaskHybrid,
              ∀ i : Fin p.input.rootSize,
                t (Fin.castAdd p.mask.size i) = g i
        exact ⟨hGraph, old, fun i => Fin.append_left root out i⟩
      have hPrefix : ∀ i : Fin p.input.rootSize,
          t (Fin.castAdd p.mask.size i) = e i :=
        fun i => Fin.append_left root out i
      refine ⟨t, ⟨hTag, hPrefix⟩, ?_⟩
      intro ys hValid
      have hOther :
          (A.toStructure.toNonemptyPartial.wholeMaskPatternGraph
            A.part).rel (.inr (.inr (p.input, p.mask))) ys :=
        hValid.1.1
      have hRootSame : ∀ i : Fin p.input.rootSize,
          ys (Fin.castAdd p.mask.size i) =
            t (Fin.castAdd p.mask.size i) := by
        intro i
        calc
          ys (Fin.castAdd p.mask.size i) = e i := hValid.2 i
          _ = t (Fin.castAdd p.mask.size i) := (hPrefix i).symm
      exact
        A.toStructure.toNonemptyPartial.wholeMaskPatternGraph_unique_outputs
          A.part hTransNative p.input p.mask ys t
          hOther hGraph hRootSame

end StructuralRamsey.FunctionalPartite
