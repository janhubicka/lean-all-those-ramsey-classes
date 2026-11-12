import AllThoseRamseyClasses.Published.TrackEHybridFullSplitRootTags
import PartiteConstruction.Functional.OutputPartSingletonization

/-!
# Track E2: the CANONICAL hybrid full-root split-tag expansion is U-CLOSED

The hybrid root index in #1062 records the ENTIRE induced hybrid
input-root relational structure. For a genuine native partite
System A, each split output-part function (F,q) is singleton-valued.

Given an embedding of one of the full hybrid roots in the canonical
source, the source domain relation asserts that its split fibre is
nonempty. This yields one output y and hence one fresh full-root
closure tuple over the exact input root. Any other closure tuple
over that root has another output y' in the same split primitive
fibre; singleton-valuedness forces y'=y. Root coordinates are
already fixed by the embedding.

We also prove the irreducible-root coverage axiom built into #1062,
not an artificial empty-root substitute. The statement covers all
positive distinct-input root patterns, including repeated primitive
input coordinates, without changing the native vertex carrier.

This proves U-closedness ONLY for the NEW SPLIT hybrid full-root
closure description in #1062. The complete original multivalued
OLD-mask full-root closure rules, combined closure description,
hybrid strong-amalgamation and sparse Ramsey witness remain separate.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.Language

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Every native partite source's hybrid full split-root tagging
satisfies each true 2019 U-closure rule indexed by a FULL hybrid
root. The root is an exact old input equality pattern and the
unique output is controlled by canonical singletonization.
No extra vertices, generated hull or old-mask closure oracle. -/
theorem System.splitMaskHybridFullSplitRoot_isUClosed
    (A : System L Parts V) :
    IsUClosed
      (L.splitMaskHybridSplitClosureRules Parts)
      (splitMaskHybridFullRootExpansion A.splitMaskHybrid) := by
  classical
  intro rule hrule
  obtain ⟨p, rfl⟩ := hrule
  constructor
  · intro t ht
    change A.splitMaskHybrid.rel
        (hybridSplitOutputSymbol p.input) t ∧
        ∃ e : Embedding p.root A.splitMaskHybrid,
          ∀ i : Fin p.input.rootSize, t i.castSucc = e i at ht
    obtain ⟨_, e, he⟩ := ht
    exact ⟨e.splitMaskHybridFullRoot, he⟩
  · intro e
    let old : Embedding p.root A.splitMaskHybrid :=
      e.splitMaskHybridFullRootReduct
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
    let xs : Fin (p.input.rootSize + 1) → V :=
      Structure.funcTuple root y
    have hTag :
        (splitMaskHybridFullRootExpansion A.splitMaskHybrid).rel
          (.inr p) xs := by
      change A.splitMaskHybrid.rel
          (hybridSplitOutputSymbol p.input) xs ∧
          ∃ g : Embedding p.root A.splitMaskHybrid,
            ∀ i : Fin p.input.rootSize, xs i.castSucc = g i
      constructor
      · change
          Function.Injective
            (fun i : Fin p.input.rootSize => xs i.castSucc) ∧
          xs (Fin.last p.input.rootSize) ∈
            (A.splitOutputParts).toStructure.func p.input.symbol
              ((fun i : Fin p.input.rootSize => xs i.castSucc) ∘
                p.input.argMap)
        simpa only [xs, Structure.funcTuple_castSucc,
          Structure.funcTuple_last] using
          (show Function.Injective root ∧
            y ∈ (A.splitOutputParts).toStructure.func
              p.input.symbol (root ∘ p.input.argMap)
            from ⟨hInj, hy⟩)
      · refine ⟨old, ?_⟩
        intro i
        exact Structure.funcTuple_castSucc root y i
    have hPrefix :
        ∀ i : Fin p.input.rootSize, xs i.castSucc = e i := by
      intro i
      change xs i.castSucc = root i
      exact Structure.funcTuple_castSucc root y i
    refine ⟨xs, ⟨hTag, hPrefix⟩, ?_⟩
    intro ys hValid
    have hPrefixY : ∀ i : Fin p.input.rootSize,
        ys i.castSucc = root i := by
      intro i
      exact hValid.2 i
    have hOutput :
        ys (Fin.last p.input.rootSize) ∈
          (A.splitOutputParts).toStructure.func
            p.input.symbol (root ∘ p.input.argMap) := by
      have hGraph : A.splitMaskHybrid.rel
          (hybridSplitOutputSymbol p.input) ys :=
        hValid.1.1
      change
        Function.Injective
          (fun i : Fin p.input.rootSize => ys i.castSucc) ∧
        ys (Fin.last p.input.rootSize) ∈
          (A.splitOutputParts).toStructure.func p.input.symbol
            ((fun i : Fin p.input.rootSize => ys i.castSucc) ∘
              p.input.argMap) at hGraph
      have hRoot : (fun i : Fin p.input.rootSize => ys i.castSucc) =
          root := funext hPrefixY
      rw [hRoot] at hGraph
      exact hGraph.2
    have hLast :
        ys (Fin.last p.input.rootSize) = y :=
      A.splitOutputParts_singletonValued
        p.input.symbol (root ∘ p.input.argMap)
        _ _ hOutput hy
    apply funext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [xs, Structure.funcTuple_last] using hLast
    · simpa only [xs, Structure.funcTuple_castSucc] using hPrefixY j

/-- The new tag layer forgets back to the literal original canonical
hybrid source, without modifying any of the OLD masks, positive split
graph incidences, or unary part predicates. -/
theorem System.splitMaskHybridFullSplitRoot_reduct
    (A : System L Parts V) :
    splitMaskHybridFullRootReduct
      (splitMaskHybridFullRootExpansion A.splitMaskHybrid) =
      A.splitMaskHybrid := rfl

end StructuralRamsey.FunctionalPartite
