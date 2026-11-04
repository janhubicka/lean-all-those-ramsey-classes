import AllThoseRamseyClasses.Lifts.NestedGeometricOuterExteriorPrivate
import AllThoseRamseyClasses.Lifts.FullFreeAmalgamPrivateOuterComponentIff
import AllThoseRamseyClasses.Lifts.FullFreeAmalgamPrivateGeneratedBoundary
import AllThoseRamseyClasses.Lifts.GeometricRetainedInteriorPath

/-!
# Reflect an older exterior's entire generated root into the retained complement

The conditional reconstructed outer-piece theorem needs the retained
complement's old exterior to have exact internal generated boundary T.
For actual nested geometric pieces of the ORIGINAL forbidden source,
this follows from the original outer minimal closed separator.

General reflection lemma:
- in Old = Inner +_U Complement, take a COMPLETE Old-minus-T
  component based at a Complement vertex;
- if that WHOLE component avoids every U-root vertex, each path
  vertex is on the Complement side, and private-side full Gaifman
  adjacency reflects every step into Complement;
- consequently the complete whole component is EXACTLY the image of
  the Complement-minus-T component;
- the verified native private-set generated-boundary transport,
  together with FULL embedding injectivity, reflects the complete
  equation Cl_Old(N(C)) = image(T) back to Cl_Comp(N(C_comp)) = T.

For genuine nested pieces, the previously verified source privacy
lemma supplies avoidance of U for the older opposite exterior, and
the older geometric minimal-separator equation supplies its
whole-source generated boundary. No root-comparability hypothesis,
target weak-map injectivity or graph-only approximation is used.

This is source geometry; it does NOT assert that the complete new
outer context has the old all-test rooted incompatibility profile,
nor Claim 2's strictly descending local B-source support.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- If a whole older-cut exterior component is private to the
shared gluing root in an ACTUAL full functional free amalgam,
its complete generated boundary reflects into the retained side.

This does not assume T contains U or U contains T. Crucially the
external boundary equality is supplied only in Whole, not assumed
in the private side. -/
theorem fullFreeAmalgam_privateExterior_internalBoundary_reflection
    {H E B W : Type v}
    {Root : Structure L H}
    {Inner : Structure L E}
    {Complement : Structure L B}
    {Whole : Structure L W}
    {sInner : Structure.Embedding Root Inner}
    {sComp : Structure.Embedding Root Complement}
    {iInner : Structure.Embedding Inner Whole}
    {iComp : Structure.Embedding Complement Whole}
    (hFree : Structure.IsFreeAmalgam
      sInner sComp iInner iComp)
    (T : Set B)
    (x : {b : B // b ∉ T})
    (hWholePrivate :
      componentFrom Whole.graph (iComp '' T)
        (fullFunctionalEmbedding_outsideCut iComp T x) ⊆
        {w : W | w ∉ iComp '' Set.range sComp})
    (hWholeBoundary :
      Whole.functionClosure
        (gaifmanNeighborhood Whole.graph
          (componentFrom Whole.graph (iComp '' T)
            (fullFunctionalEmbedding_outsideCut iComp T x))) =
      iComp '' T) :
    (componentFrom Complement.graph T x ⊆
      {b : B | b ∉ Set.range sComp}) ∧
    Complement.functionClosure
      (gaifmanNeighborhood Complement.graph
        (componentFrom Complement.graph T x)) = T := by
  let CWhole : Set W :=
    componentFrom Whole.graph (iComp '' T)
      (fullFunctionalEmbedding_outsideCut iComp T x)
  let CComp : Set B :=
    componentFrom Complement.graph T x
  have hLift :
      ∀ (y : {w : W // w ∉ iComp '' T}),
        ReachOutside Whole.graph (iComp '' T)
          (fullFunctionalEmbedding_outsideCut iComp T x) y →
        ∃ b : {b : B // b ∉ T},
          y.1 = iComp b.1 ∧
          ReachOutside Complement.graph T x b := by
    intro y hPath
    induction hPath with
    | refl =>
        exact ⟨x, rfl, Relation.ReflTransGen.refl⟩
    | @tail p q hp hedge ih =>
        obtain ⟨b, hpb, hpB⟩ := ih
        have hpInC : p.1 ∈ CWhole := ⟨p.2, hp⟩
        have hpNotU : p.1 ∉ iComp '' Set.range sComp :=
          hWholePrivate hpInC
        have hbPrivate : b.1 ∉ Set.range sComp := by
          intro hbRoot
          exact hpNotU ⟨b.1, hbRoot, hpb.symm⟩
        have hEdge : GaifmanAdjacent Whole.graph (iComp b.1) q.1 := by
          change GaifmanAdjacent Whole.graph p.1 q.1 at hedge
          rw [hpb] at hedge
          exact hedge
        have hqInComp : q.1 ∈ Set.range iComp :=
          fullFreeAmalgam_leftPrivate_neighbor_in_left
            hFree.swap b.1 hbPrivate q.1 hEdge
        obtain ⟨c, hcEq⟩ := hqInComp
        have hcNotT : c ∉ T := by
          intro hcT
          exact q.2 ⟨c, hcT, hcEq⟩
        have hEdgeComp :
            GaifmanAdjacent Complement.graph b.1 c :=
          (fullFreeAmalgam_rightPrivate_gaifmanAdjacent_iff
            hFree b.1 c hbPrivate).mp (by
              rw [← hcEq]
              exact hEdge)
        exact ⟨⟨c, hcNotT⟩, hcEq.symm, hpB.tail hEdgeComp⟩
  have hComponents : CWhole = iComp '' CComp := by
    apply Set.Subset.antisymm
    · intro w hw
      let y : {w : W // w ∉ iComp '' T} := ⟨w, hw.1⟩
      obtain ⟨b, hEq, hPath⟩ := hLift y hw.2
      exact ⟨b.1, ⟨b.2, hPath⟩, hEq.symm⟩
    · rintro w ⟨b, hb, rfl⟩
      have hPath :
          ReachOutside Whole.graph (iComp '' T)
            (fullFunctionalEmbedding_outsideCut iComp T x)
            (fullFunctionalEmbedding_outsideCut iComp T
              ⟨b, hb.1⟩) :=
        fullFunctionalEmbedding_reachOutside_map iComp T hb.2
      exact ⟨(fullFunctionalEmbedding_outsideCut iComp T
        ⟨b, hb.1⟩).2, hPath⟩
  have hCompPrivate : CComp ⊆
      {b : B | b ∉ Set.range sComp} := by
    intro b hb hRoot
    have hbInWhole : iComp b ∈ CWhole := by
      rw [hComponents]
      exact ⟨b, hb, rfl⟩
    exact hWholePrivate hbInWhole ⟨b, hRoot, rfl⟩
  have hGenerated :
      Whole.functionClosure
        (gaifmanNeighborhood Whole.graph (iComp '' CComp)) =
      iComp '' (Complement.functionClosure
        (gaifmanNeighborhood Complement.graph CComp)) :=
    fullFreeAmalgam_private_generatedBoundary_eq_image
      hFree (Set.range sComp) CComp
      (fun r => ⟨r, rfl⟩) hCompPrivate
  have hBoundaryImages :
      iComp '' (Complement.functionClosure
        (gaifmanNeighborhood Complement.graph CComp)) =
      iComp '' T := by
    change Whole.functionClosure
      (gaifmanNeighborhood Whole.graph CWhole) =
      iComp '' T at hWholeBoundary
    rw [hComponents] at hWholeBoundary
    exact hGenerated.symm.trans hWholeBoundary
  refine ⟨hCompPrivate, ?_⟩
  apply Set.Subset.antisymm
  · intro b hb
    have hbImage : iComp b ∈
        iComp '' (Complement.functionClosure
          (gaifmanNeighborhood Complement.graph CComp)) :=
      ⟨b, hb, rfl⟩
    rw [hBoundaryImages] at hbImage
    obtain ⟨c, hc, hcEq⟩ := hbImage
    have hcb : c = b := iComp.injective hcEq
    exact hcb ▸ hc
  · intro b hb
    have hbImage : iComp b ∈ iComp '' T :=
      ⟨b, hb, rfl⟩
    rw [← hBoundaryImages] at hbImage
    obtain ⟨c, hc, hcEq⟩ := hbImage
    have hcb : c = b := iComp.injective hcEq
    exact hcb ▸ hc

/-- The old opposite exterior's COMPLETE internal native generated
boundary follows automatically from actual nesting of two original
minimal closed separator pieces.

The old outer cut is transported to the true unchanged full
complement as an exact preimage; no extra closedness or privacy
assumption remains. This is the previously missing retained
exterior hypothesis in the geometric reconstruction of #834. -/
theorem nestedGeometric_originalExterior_internalBoundary_eq_outerRoot
    {V : Type}
    (Old : Structure L V)
    {n m : ℕ}
    (inner : GeometricFunctionalPieceData Old n)
    (outer : GeometricFunctionalPieceData Old m)
    (hNested :
      componentFrom Old.graph (Set.range inner.roots) inner.left ⊆
        componentFrom Old.graph (Set.range outer.roots) outer.left) :
    let Comp := geometricGlobalComplementChart Old inner
    let iComp : Structure.Embedding Comp.str Old :=
      functionalComponentComplementEmbedding Old
        (Set.range inner.roots) inner.minimal.1 inner.left
    let T : Set Comp.Carrier := iComp ⁻¹' Set.range outer.roots
    Comp.str.IsClosed T ∧
      ∃ x : {b : Comp.Carrier // b ∉ T},
        (componentFrom Comp.str.graph T x ⊆
          {b : Comp.Carrier | b ∉ Set.range Comp.rootEmbedding}) ∧
        Comp.str.functionClosure
          (gaifmanNeighborhood Comp.str.graph
            (componentFrom Comp.str.graph T x)) = T := by
  let Comp := geometricGlobalComplementChart Old inner
  let iComp : Structure.Embedding Comp.str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range inner.roots) inner.minimal.1 inner.left
  let T : Set Comp.Carrier :=
    iComp ⁻¹' Set.range outer.roots
  have hOuterRootOutside : ∀ i : Fin m,
      outer.roots i ∉
        functionalComponentFrom Old (Set.range inner.roots) inner.left :=
    nestedGeometric_outerRoot_avoids_innerComponent
      Old inner outer hNested
  have hTclosed : Comp.str.IsClosed T :=
    functionalEmbedding_preimage_closed
      Comp.str Old iComp (Set.range outer.roots) outer.minimal.1
  have hTRange : iComp '' T = Set.range outer.roots := by
    apply Set.Subset.antisymm
    · rintro w ⟨b, hb, rfl⟩
      exact hb
    · rintro w ⟨i, rfl⟩
      exact ⟨⟨outer.roots i, hOuterRootOutside i⟩,
        ⟨i, rfl⟩, rfl⟩
  have hRightInExterior :
      outer.right.1 ∈
        componentFrom Old.graph (Set.range outer.roots) outer.right :=
    componentFrom_root Old.graph (Set.range outer.roots) outer.right
  have hRightOutside :
      outer.right.1 ∉
        functionalComponentFrom Old (Set.range inner.roots) inner.left :=
    (nestedGeometric_outerExterior_avoids_innerPiece
      Old inner outer hNested outer.right.1 hRightInExterior).2
  let x : {b : Comp.Carrier // b ∉ T} :=
    ⟨⟨outer.right.1, hRightOutside⟩, outer.right.2⟩
  let xWhole : {w : V // w ∉ iComp '' T} :=
    fullFunctionalEmbedding_outsideCut iComp T x
  have hSame :
      componentFrom Old.graph (iComp '' T) xWhole =
      componentFrom Old.graph (Set.range outer.roots) outer.right :=
    sourceGaifmanComponent_eq_of_cut_eq
      Old hTRange xWhole outer.right rfl
  have hInnerRootRange :
      iComp '' Set.range Comp.rootEmbedding =
        Set.range inner.roots :=
    geometricGlobalSource_innerRoot_range_eq Old inner
  have hWholePrivate :
      componentFrom Old.graph (iComp '' T) xWhole ⊆
        {w : V | w ∉ iComp '' Set.range Comp.rootEmbedding} := by
    intro w hw
    have hwExterior :
        w ∈ componentFrom Old.graph
          (Set.range outer.roots) outer.right := by
      rw [← hSame]
      exact hw
    have hwOutsideInnerRoot :
        w ∉ Set.range inner.roots :=
      (nestedGeometric_outerExterior_avoids_innerPiece
        Old inner outer hNested w hwExterior).1
    rw [hInnerRootRange]
    exact hwOutsideInnerRoot
  have hWholeBoundary :
      Old.functionClosure
        (gaifmanNeighborhood Old.graph
          (componentFrom Old.graph (iComp '' T) xWhole)) =
        iComp '' T := by
    rw [hSame, hTRange]
    exact geometricPiece_right_boundary_closure Old outer
  obtain ⟨hCompPrivate, hCompBoundary⟩ :=
    fullFreeAmalgam_privateExterior_internalBoundary_reflection
      (geometricGlobalSource_freeDiagram Old inner)
      T x hWholePrivate hWholeBoundary
  exact ⟨hTclosed, x, hCompPrivate, hCompBoundary⟩

end AllThoseRamseyClasses.Lifts
