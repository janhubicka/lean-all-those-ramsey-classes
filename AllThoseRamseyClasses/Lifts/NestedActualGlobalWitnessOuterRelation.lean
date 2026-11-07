import AllThoseRamseyClasses.Lifts.NestedSelectedOuterTargetRelation
import AllThoseRamseyClasses.Lifts.SelectedGlobalFlipGeometricWitness
import AllThoseRamseyClasses.Lifts.CanonicalGlueDiagramBridge
import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram

/-!
# Actual global canonical witness produces the nested outer relation after flipping

This bridges two already-distinguished interfaces of the original
2019 Section 3 argument.

On the input side we have the ORIGINAL global canonical relation
for the inner source piece, realized in a second witness B, and a
genuine weak map of the old forbidden source into the target.
The verified selected-global source-flip theorem extracts an actual
geometrically selected replacement Q, its canonical-gluing
incompatibility equivalence, and the literal new forbidden FULL
functional free-amalgam source. The verified gluing/diagram bridge
converts the returned canonical-gluing profile into precisely
the diagram equivalence used by the nested outer-symbol theorem.

On the output side the new weak map agrees with the original map on
EVERY unchanged complement vertex. The nested source-symbol theorem
and geometric global relation realization therefore yield the
ORIGINAL older outer piece relation at the original target root tuple.

Injectivity of the OLD outer root under the old weak map remains an
EXPLICIT hypothesis. It is neither inferred from injectivity of the
inner global tuple nor from weak EHN properties. This is the distinct
Track D root-collision obligation. This theorem does not establish
the terminating local B-source-support descent of Track C.

This module is an unvalidated integration until the exact-head full
Lean build and named #print axioms check have passed.
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
  obtain ⟨Q, hRootPieceEquiv, hSelected,
      g, hg, hgRoots,
      W, New, hFNew, iQ, iT, hFree,
      flip, hFlip, hQMap, hTMap⟩ :=
    selectedGlobalCanonicalDiagramFlip_geometricWitness
      F P hn T hOldDiagram
      B Target jB xsB hGlobalP pT hpT hRootAgree
  have hDiagramEquiv :
      (functionalDiagramPieceSetoid
        (geometricGlobalFunctionalChart Old inner).root F).r
        (geometricGlobalFunctionalChart Old inner).ext Q :=
    (functionalDiagramPiece_equiv_iff_glue
      P.1.root F P.1.ext Q).mpr hRootPieceEquiv
  have hOuterSurvives : ∀ i : Fin m,
      outer.roots i ∉
        functionalComponentFrom Old
          (Set.range inner.roots) inner.left :=
    nestedGeometric_outerRoot_avoids_innerComponent
      Old inner outer hNested
  let oldOuterT : Fin m → T.Carrier :=
    fun i => ⟨outer.roots i, hOuterSurvives i⟩
  have hRetainedCoordinates (i : Fin m) :
      flip (iT (oldOuterT i)) = f (outer.roots i) := by
    exact hTMap (oldOuterT i)
  have hOuterFlipInjective :
      Function.Injective
        (fun i : Fin m => flip (iT (oldOuterT i))) := by
    intro i j hij
    apply hOldOuterRootInjective
    calc
      f (outer.roots i) = flip (iT (oldOuterT i)) :=
        (hRetainedCoordinates i).symm
      _ = flip (iT (oldOuterT j)) := hij
      _ = f (outer.roots j) := hRetainedCoordinates j
  have hOriginalRelation :
      (globalFunctionalCanonicalLift F Target).rel
        (.inr (geometricGlobalPieceSymbol F Old
          (inferInstance : Finite V) hFOld outer hm))
        (fun i : Fin m => flip (iT (oldOuterT i))) :=
    nestedGeometric_selectedFlip_preserves_outerGlobalRelation_in_target
      F Old hFOld inner outer hNested
      Q hSelected hDiagramEquiv New hFNew iQ iT hFree
      hm Target flip hFlip hOuterFlipInjective
  have hActualTuple :
      (fun i : Fin m => flip (iT (oldOuterT i))) =
        (fun i : Fin m => f (outer.roots i)) :=
    funext hRetainedCoordinates
  have hOriginalAtOldTuple :
      (globalFunctionalCanonicalLift F Target).rel
        (.inr (geometricGlobalPieceSymbol F Old
          (inferInstance : Finite V) hFOld outer hm))
        (fun i : Fin m => f (outer.roots i)) := by
    rw [← hActualTuple]
    exact hOriginalRelation
  refine ⟨Q, W, New, iQ, iT, flip, hFNew, hFree, hFlip, ?_,
    hOriginalAtOldTuple⟩
  intro b
  exact hTMap b

end AllThoseRamseyClasses.Lifts
