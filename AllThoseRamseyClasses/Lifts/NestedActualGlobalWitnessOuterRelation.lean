import AllThoseRamseyClasses.Lifts.SelectedGlobalFlipGeometricWitness
import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram
import AllThoseRamseyClasses.Lifts.GeometricGlobalPieceSymbol

/-!
# Actual global canonical witness produces the nested outer relation after flipping

This bridges two already-distinguished interfaces of the original
2019 Section 3 argument.

On the input side we have the ORIGINAL global canonical relation
for the inner source piece, realized in a second witness B, and a
genuine weak map of the old forbidden source into the target.
The verified selected-global source-flip theorem extracts an actual
geometrically selected replacement Q and a literal new forbidden
FULL functional free-amalgam source, together with its weak map.
The returned gluing-profile equivalence remains a valid certificate,
but this theorem does not need to invoke the separate nested
outer-symbol transport to prove its original-target relation.

On the output side the new weak map agrees with the original map on
EVERY unchanged complement vertex. The target relation at the
ORIGINAL older outer piece is in fact independent of the flip:
the input weak map `f : Old → Target` already realizes this relation
whenever the original older root's target-image tuple is injective,
by `geometricGlobalCanonicalRelation_of_weak`.
There is no reason to re-prove nested source-symbol preservation
to derive a relation which was already true in the input target.

Injectivity of the OLD outer root under the old weak map remains an
EXPLICIT hypothesis. It is neither inferred from injectivity of the
inner global tuple nor from weak EHN properties. This is the distinct
Track D root-collision obligation. This theorem does not establish
the terminating local B-source-support descent of Track C.

The direct-target-relation shortening (#972) was independently
exact-head Lean CI-verified and merged without changing this theorem's
statement. Its genuinely nontrivial source-flip construction still
uses `selectedGlobalCanonicalDiagramFlip_geometricWitness`.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V UB UT : Type}

/-- A REAL original inner global canonical relation in the second
witness produces a literal forbidden replacement source with a weak
target map that preserves the original older GLOBAL relation.

The source is genuinely selected, and the only independent target
injectivity premise concerns the *original older* outer root image.
The original outer target relation follows directly from the input
`Old.IsEHNHomomorphismEmbedding Target f` and this injection,
independently of the replacement. The historical `hNested`
parameter is retained for API compatibility, but is not needed
by either the source replacement or this target relation.
No arbitrary selected Q, selected geometry, profile-equivalence,
or new-source existence hypothesis remains in this theorem statement. -/
theorem nestedGeometric_actualGlobalWitness_preserves_outerRelation
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    [Finite V]
    (Old : Structure L V) (hFOld : F Old)
    {n m : ℕ}
    (inner : GeometricFunctionalPieceData Old n)
    (outer : GeometricFunctionalPieceData Old m)
    (hNested :
      componentFrom Old.graph (Set.range inner.roots) inner.left ⊆
        componentFrom Old.graph (Set.range outer.roots) outer.left)
    (hn : 0 < n) (hm : 0 < m)
    (Target : Structure L UT)
    (f : V → UT) (hf : Old.IsEHNHomomorphismEmbedding Target f)
    (B : Structure L UB)
    (jB : Structure.Embedding B Target)
    (xsB : Fin n → UB)
    (hInnerGlobal :
      (globalFunctionalCanonicalLift F B).rel
        (.inr (geometricGlobalPieceSymbol F Old
          (inferInstance : Finite V) hFOld inner hn)) xsB)
    (hInnerCoordinates : ∀ i : Fin n,
      jB (xsB i) = f (inner.roots i))
    (hOldOuterRootInjective :
      Function.Injective (fun i : Fin m => f (outer.roots i))) :
    let T := geometricGlobalComplementChart Old inner
    ∃ (Q : FunctionalRootExtension
          (geometricGlobalFunctionalChart Old inner).root)
      (W : Type) (New : Structure L W)
      (iQ : Structure.Embedding Q.str New)
      (iT : Structure.Embedding T.str New)
      (flip : W → UT),
      F New ∧
      Structure.IsFreeAmalgam Q.rootEmbedding T.rootEmbedding iQ iT ∧
      New.IsEHNHomomorphismEmbedding Target flip ∧
      (∀ b : T.Carrier, flip (iT b) = f b.1) ∧
      (globalFunctionalCanonicalLift F Target).rel
        (.inr (geometricGlobalPieceSymbol F Old
          (inferInstance : Finite V) hFOld outer hm))
        (fun i : Fin m => f (outer.roots i)) := by
  let P : SelectedFunctionalChart F n :=
    geometricGlobalSelectedChart F Old
      (inferInstance : Finite V) hFOld inner
  let T := geometricGlobalComplementChart Old inner
  let iOldT : Structure.Embedding T.str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range inner.roots) inner.minimal.1 inner.left
  let pT : T.Carrier → UT := fun b => f b.1
  have hpT : T.str.IsEHNHomomorphismEmbedding Target pT :=
    hf.comp iOldT.isEHNHomomorphismEmbedding
  have hOldDiagram :
      forbiddenFunctionalDiagram P.1.root F P.1.ext T :=
    geometricGlobalSource_has_forbidden_diagram F Old
      (inferInstance : Finite V) hFOld inner
  have hGlobalP :
      (globalFunctionalCanonicalLift F B).rel
        (.inr (globalPieceSymbolOf F P hn)) xsB := by
    change (globalFunctionalCanonicalLift F B).rel
      (.inr (geometricGlobalPieceSymbol F Old
        (inferInstance : Finite V) hFOld inner hn)) xsB
    exact hInnerGlobal
  have hRootAgree : ∀ i : Fin n,
      jB (xsB i) = pT (T.rootEmbedding i) := by
    intro i
    calc
      jB (xsB i) = f (inner.roots i) := hInnerCoordinates i
      _ = pT (T.rootEmbedding i) := rfl
  obtain ⟨Q, _hRootPieceEquiv, _hSelected,
      _g, _hg, _hgRoots,
      W, New, hFNew, iQ, iT, hFree,
      flip, hFlip, _hQMap, hTMap⟩ :=
    selectedGlobalCanonicalDiagramFlip_geometricWitness
      F P hn T hOldDiagram
      B Target jB xsB hGlobalP pT hpT hRootAgree
  have hOriginalAtOldTuple :
      (globalFunctionalCanonicalLift F Target).rel
        (.inr (geometricGlobalPieceSymbol F Old
          (inferInstance : Finite V) hFOld outer hm))
        (fun i : Fin m => f (outer.roots i)) :=
    geometricGlobalCanonicalRelation_of_weak
      F Old (inferInstance : Finite V) hFOld outer hm
      Target f hf hOldOuterRootInjective
  exact ⟨Q, W, New, iQ, iT, flip,
    hFNew, hFree, hFlip, hTMap, hOriginalAtOldTuple⟩

end AllThoseRamseyClasses.Lifts
