import AllThoseRamseyClasses.Lifts.OuterContextCarrierFromSelectedInnerComponent
import AllThoseRamseyClasses.Lifts.GeometricInnerSourceInterface
import AllThoseRamseyClasses.Lifts.GeometricInnerRootOuterBoundary
import AllThoseRamseyClasses.Lifts.GeometricRetainedInteriorPath
import AllThoseRamseyClasses.Lifts.GlobalFlipClosedOuterContext

/-!
# Exact transported older context carrier in a genuine nested source flip

The abstract carrier theorem for two literal native functional free
amalgams requires old-side selected-component geometry and attachment
of all surviving inner roots to an older outer component.

For an ACTUAL nested pair of source-attached geometric
minimal-closed-separator pieces, these are not new assumptions.
We recover the precise old full source diagram, the original
inner private-component geometry, the entire older root as an
exact closed preimage in the unchanged complement, and the whole
older outer component with the genuine chosen inner vertex.

The selected replacement Q needs two independent properties:
the chosen private component generates the COMPLETE full inner
root, and ALL Q-private vertices lie in that one component.
The first holds for genuine canonical selected replacements by
the merged selected-Q boundary proof; the second is addressed
independently in #881 and is not inferred from the boundary.

The conclusion is an EXACT equation of actual native source
carrier sets:

  iQ[all Q] ∪ iE[E ∩ (old outer geometric piece)] =
    iE[old outer cut] ∪ component(New minus old outer cut, iQ(q)).

It is not merely an isomorphism, not an equality of images in a
noninjective weak forbidden target map, and makes no assumption
that the old/inner cuts are nested.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V W : Type}


/-- A root-complement that has one component containing ALL private
vertices has the same property when rooted at ANY other surviving
private vertex. This re-rooting is needed because the selected-Q
complete-boundary witness (#805) and its all-private connectivity
witness (#881) need not be the SAME chosen private vertex.

The theorem preserves actual root-avoiding Gaifman paths; it never
identifies vertices through a weak target image. -/
theorem functionalAllPrivate_component_reroot
    (A : Structure L V) (U : Set V)
    (x y : {v : V // v ∉ U})
    (hAll : ∀ v : V, v ∉ U →
      v ∈ componentFrom A.graph U x) :
    ∀ v : V, v ∉ U →
      v ∈ componentFrom A.graph U y := by
  have hyFromX : y.1 ∈ componentFrom A.graph U x :=
    hAll y.1 y.2
  have hyToX : ReachOutside A.graph U y x :=
    reachOutside_symm A.graph U hyFromX.2
  intro v hv
  have hvFromX : v ∈ componentFrom A.graph U x :=
    hAll v hv
  exact ⟨hv, hyToX.trans hvFromX.2⟩

/-- A genuine original older geometric piece containing the selected
inner component has its FULL transplanted context exactly equal to
the transported old root plus one actual new T-component.

There is no independent old-root attachment premise, no retained
component-membership assumption, and no arbitrary context identity.
The selected Q is assumed to have one complete generated root
component containing ALL its private vertices; genuine selected
canonical witnesses discharge these separately. -/
theorem nestedGeometric_actualTransportContext_eq_outerComponent
    (Old : Structure L V)
    {n m : ℕ}
    (inner : GeometricFunctionalPieceData Old n)
    (outer : GeometricFunctionalPieceData Old m)
    (hNested :
      componentFrom Old.graph (Set.range inner.roots) inner.left ⊆
        componentFrom Old.graph (Set.range outer.roots) outer.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (dQ : {q : Q.Carrier // q ∉ Set.range Q.rootEmbedding})
    (hQBoundary :
      Q.str.functionClosure
        (gaifmanNeighborhood Q.str.graph
          (componentFrom Q.str.graph
            (Set.range Q.rootEmbedding) dQ)) =
        Set.range Q.rootEmbedding)
    (hAllQ : ∀ q : Q.Carrier,
      q ∉ Set.range Q.rootEmbedding →
        q ∈ componentFrom Q.str.graph
          (Set.range Q.rootEmbedding) dQ) :
    let Comp := geometricGlobalComplementChart Old inner
    let oldE : Structure.Embedding Comp.str Old :=
      functionalComponentComplementEmbedding Old
        (Set.range inner.roots) inner.minimal.1 inner.left
    let T : Set Comp.Carrier :=
      oldE ⁻¹' Set.range outer.roots
    ∃ xNew : {w : W // w ∉ iE '' T},
      xNew.1 = iQ dQ.1 ∧
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' oldOuterContextInInnerComplement Old outer inner) =
      (iE '' T) ∪
        componentFrom New.graph (iE '' T) xNew := by
  let P := geometricGlobalFunctionalChart Old inner
  let Comp := geometricGlobalComplementChart Old inner
  let iOldP : Structure.Embedding P.ext.str Old :=
    functionalComponentEmbedding Old (Set.range inner.roots)
      inner.minimal.1 inner.left
  let oldE : Structure.Embedding Comp.str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range inner.roots) inner.minimal.1 inner.left
  let T : Set Comp.Carrier :=
    oldE ⁻¹' Set.range outer.roots
  have hTclosed : Comp.str.IsClosed T :=
    functionalEmbedding_preimage_closed
      Comp.str Old oldE (Set.range outer.roots) outer.minimal.1
  have hOuterRootOutside : ∀ j : Fin m,
      outer.roots j ∉
        functionalComponentFrom Old
          (Set.range inner.roots) inner.left := by
    intro j hj
    have hjOuter : outer.roots j ∈
        componentFrom Old.graph (Set.range outer.roots) outer.left :=
      hNested hj
    exact hjOuter.1 ⟨j, rfl⟩
  have hTRange : oldE '' T = Set.range outer.roots := by
    apply Set.Subset.antisymm
    · rintro z ⟨e, he, rfl⟩
      exact he
    · rintro z ⟨j, rfl⟩
      exact ⟨⟨outer.roots j, hOuterRootOutside j⟩,
        ⟨j, rfl⟩, rfl⟩
  have hInnerInOuter :
      inner.left.1 ∈
        componentFrom Old.graph (Set.range outer.roots) outer.left :=
    hNested
      (componentFrom_root Old.graph (Set.range inner.roots) inner.left)
  let xOld : {v : V // v ∉ oldE '' T} :=
    ⟨inner.left.1, by
      rw [hTRange]
      exact hInnerInOuter.1⟩
  let xOuter : {v : V // v ∉ Set.range outer.roots} :=
    ⟨inner.left.1, hInnerInOuter.1⟩
  have hOldCutComponent :
      componentFrom Old.graph (Set.range outer.roots) xOuter =
      componentFrom Old.graph (Set.range outer.roots) outer.left := by
    apply Set.Subset.antisymm
    · intro z hz
      exact ⟨hz.1, hInnerInOuter.2.trans hz.2⟩
    · intro z hz
      exact ⟨hz.1,
        (reachOutside_symm Old.graph (Set.range outer.roots)
          hInnerInOuter.2).trans hz.2⟩
  have hSameOldOuter :
      componentFrom Old.graph (oldE '' T) xOld =
      componentFrom Old.graph (Set.range outer.roots) outer.left := by
    calc
      componentFrom Old.graph (oldE '' T) xOld =
        componentFrom Old.graph (Set.range outer.roots) xOuter :=
          sourceGaifmanComponent_eq_of_cut_eq
            Old hTRange xOld xOuter rfl
      _ = componentFrom Old.graph
          (Set.range outer.roots) outer.left := hOldCutComponent
  have hOldRootImage :
      oldE '' Set.range Comp.rootEmbedding =
        Set.range inner.roots :=
    geometricGlobalSource_innerRoot_range_eq Old inner
  let dOld : {v : V //
      v ∉ oldE '' Set.range Comp.rootEmbedding} :=
    ⟨inner.left.1, by
      rw [hOldRootImage]
      exact inner.left.2⟩
  have hOldInnerComponent :
      componentFrom Old.graph
        (oldE '' Set.range Comp.rootEmbedding) dOld =
      componentFrom Old.graph (Set.range inner.roots) inner.left :=
    sourceGaifmanComponent_eq_of_cut_eq
      Old hOldRootImage dOld inner.left rfl
  have hdOldInner : dOld.1 ∈ Set.range iOldP := by
    let e : P.ext.Carrier :=
      ⟨inner.left.1, Or.inr
        (componentFrom_root Old.graph
          (Set.range inner.roots) inner.left)⟩
    exact ⟨e, rfl⟩
  have hOldPrivateInD :
      ∀ e : P.ext.Carrier,
        e ∉ Set.range P.ext.rootEmbedding →
        iOldP e ∈ componentFrom Old.graph
          (oldE '' Set.range Comp.rootEmbedding) dOld := by
    intro e he
    have hPrivate :=
      geometricGlobalSource_innerPrivate_in_selectedComponent
        Old inner e he
    change e.1 ∈ componentFrom Old.graph
      (oldE '' Set.range Comp.rootEmbedding) dOld
    rw [hOldInnerComponent]
    exact hPrivate
  have hxOld :
      xOld.1 ∈ componentFrom Old.graph
        (oldE '' Set.range Comp.rootEmbedding) dOld := by
    rw [hOldInnerComponent]
    exact componentFrom_root Old.graph
      (Set.range inner.roots) inner.left
  have hRootAttached :
      Set.range inner.roots \ Set.range outer.roots ⊆
      componentFrom Old.graph
        (Set.range outer.roots) outer.left :=
    geometricInnerRoot_outsideOlderCut_inComponent
      Old inner (Set.range outer.roots) outer.minimal.1
      outer.left hNested
  have hRootOld :
      ∀ r : Fin n, Comp.rootEmbedding r ∉ T →
        oldE (Comp.rootEmbedding r) ∈
          componentFrom Old.graph (oldE '' T) xOld := by
    intro r hrNotT
    have hrNotOuter : inner.roots r ∉ Set.range outer.roots := by
      intro hrOuter
      apply hrNotT
      change oldE (Comp.rootEmbedding r) ∈ Set.range outer.roots
      exact hrOuter
    have hrOld :
        inner.roots r ∈
          componentFrom Old.graph
            (Set.range outer.roots) outer.left :=
      hRootAttached ⟨⟨r, rfl⟩, hrNotOuter⟩
    change inner.roots r ∈
      componentFrom Old.graph (oldE '' T) xOld
    rw [hSameOldOuter]
    exact hrOld
  obtain ⟨xNew, hxNew, hCarrier⟩ :=
    fullFreeAmalgam_outerContext_eq_of_selectedComponent
      (geometricGlobalSource_freeDiagram Old inner)
      hNewFree T hTclosed dOld hdOldInner
      hOldPrivateInD xOld hxOld hRootOld
      dQ hQBoundary hAllQ
  have hExactOldContext :
      {b : Comp.Carrier |
        oldE b ∈ (oldE '' T) ∪
          componentFrom Old.graph (oldE '' T) xOld} =
      oldOuterContextInInnerComplement Old outer inner := by
    ext b
    change
      (oldE b ∈ (oldE '' T) ∪
        componentFrom Old.graph (oldE '' T) xOld) ↔
      (oldE b ∈ geometricPieceVertices Old outer)
    rw [hSameOldOuter, hTRange]
  refine ⟨xNew, hxNew, ?_⟩
  rw [hExactOldContext] at hCarrier
  exact hCarrier

end AllThoseRamseyClasses.Lifts
