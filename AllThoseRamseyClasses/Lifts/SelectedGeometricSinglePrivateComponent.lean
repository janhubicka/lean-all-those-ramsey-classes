import AllThoseRamseyClasses.Lifts.SelectedReplacementInternalGeneratedRoot
import AllThoseRamseyClasses.Lifts.PrivateRootComponentExact
import AllThoseRamseyClasses.Lifts.GeometricInnerSourceInterface

/-!
# A genuinely selected geometric rooted piece has ONE private component

The original 2019 global piece relation uses ACTUAL rooted pieces,
not arbitrary rooted extensions with the same incompatibility profile.
A geometric source piece is the entire closed root together with ONE
connected component of the source outside that root.

Here we prove that this defining connectedness survives the genuine
induced full functional piece and ANY root-preserving full
isomorphism to a selected replacement Q.

This supplies the missing `all inserted Q-private vertices attach`
side of the exact transported-context carrier theorem (#868/#871).
In combination with the already verified complete generated-root
boundary theorem (#805), it yields ONE SAME selected Q-private
component containing EVERY private Q vertex and having its ENTIRE
native function-generated boundary equal to the full ordered root.

No weak EHN target map, graph-only induced-substructure reflection,
nested-root assumption, or root-image injectivization is used.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Reachability avoiding a deleted set is symmetric because the
native Gaifman adjacency relation is symmetric. -/
private theorem selectedPiece_reachOutside_reverse
    {V : Type} (A : Structure L V) (R : Set V)
    {x y : {v : V // v ∉ R}}
    (h : ReachOutside A.graph R x y) :
    ReachOutside A.graph R y x := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | @tail a b hpre hedge ih =>
      exact (Relation.ReflTransGen.single
        (GaifmanAdjacent.symm hedge)).trans ih

/-- Two points of one actual outside-cut component determine
exactly the same entire component, without assuming that
their root type proofs are definitionally identical. -/
private theorem selectedPiece_component_eq_of_member
    {V : Type} (A : Structure L V) (R : Set V)
    (x y : {v : V // v ∉ R})
    (hy : y.1 ∈ componentFrom A.graph R x) :
    componentFrom A.graph R x = componentFrom A.graph R y := by
  apply Set.ext
  intro z
  constructor
  · rintro ⟨hz, hreach⟩
    exact ⟨hz,
      (selectedPiece_reachOutside_reverse A R hy.2).trans hreach⟩
  · rintro ⟨hz, hreach⟩
    exact ⟨hz, hy.2.trans hreach⟩

/-- Every private vertex of a genuine selected FULL native
geometric source piece is connected to ANY private basepoint
inside that same induced piece, after removing the complete root.

The proof uses exact native full free-amalgam private-component
equality to REFLECT the original whole-source component to the
induced piece. No false induced-Gaifman edge reflection is used. -/
theorem geometricSelectedPiece_everyPrivate_connected
    {V : Type} (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n)
    (x : {e :
      (geometricGlobalFunctionalChart A d).ext.Carrier //
        e ∉ Set.range
          (geometricGlobalFunctionalChart A d).ext.rootEmbedding})
    (e : (geometricGlobalFunctionalChart A d).ext.Carrier)
    (he : e ∉ Set.range
      (geometricGlobalFunctionalChart A d).ext.rootEmbedding) :
    e ∈
      componentFrom
        (geometricGlobalFunctionalChart A d).ext.str.graph
        (Set.range
          (geometricGlobalFunctionalChart A d).ext.rootEmbedding) x := by
  classical
  let P := (geometricGlobalFunctionalChart A d).ext
  let iP : Structure.Embedding P.str A :=
    functionalComponentEmbedding A (Set.range d.roots)
      d.minimal.1 d.left
  let hFree :=
    geometricGlobalSource_freeDiagram A d
  have hRootImage :
      iP '' Set.range P.rootEmbedding = Set.range d.roots := by
    ext z
    constructor
    · rintro ⟨p, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨P.rootEmbedding i, ⟨i, rfl⟩, rfl⟩
  let xWhole : {v : V // v ∉ iP '' Set.range P.rootEmbedding} :=
    fullFunctionalEmbedding_outsideCut iP
      (Set.range P.rootEmbedding) x
  let xOld : {v : V // v ∉ Set.range d.roots} :=
    ⟨iP x.1, by
      rw [← hRootImage]
      exact xWhole.2⟩
  have hxSelected :
      xOld.1 ∈
        componentFrom A.graph (Set.range d.roots) d.left :=
    geometricGlobalSource_innerPrivate_in_selectedComponent
      A d x.1 x.2
  have hOldComponent :
      componentFrom A.graph (Set.range d.roots) d.left =
        componentFrom A.graph (Set.range d.roots) xOld :=
    selectedPiece_component_eq_of_member A
      (Set.range d.roots) d.left xOld hxSelected
  have hRootCutComponent :
      componentFrom A.graph
        (iP '' Set.range P.rootEmbedding) xWhole =
      componentFrom A.graph (Set.range d.roots) xOld :=
    sourceGaifmanComponent_eq_of_cut_eq
      A hRootImage xWhole xOld rfl
  have hFullPrivateComponent :
      componentFrom A.graph
        (iP '' Set.range P.rootEmbedding) xWhole =
      iP '' componentFrom P.str.graph
        (Set.range P.rootEmbedding) x :=
    fullFreeAmalgam_rightPrivateRoot_component_eq
      hFree.swap x
  have heOld :
      iP e ∈ componentFrom A.graph (Set.range d.roots) d.left :=
    geometricGlobalSource_innerPrivate_in_selectedComponent
      A d e he
  have heImage :
      iP e ∈ iP '' componentFrom P.str.graph
          (Set.range P.rootEmbedding) x := by
    rw [hOldComponent] at heOld
    rw [← hRootCutComponent, hFullPrivateComponent] at heOld
    exact heOld
  obtain ⟨e', he', heq⟩ := heImage
  have hee : e' = e := iP.injective heq
  simpa only [hee] using he'

/-- For EVERY genuine selected forbidden Q root extension, ALL
its private vertices lie in the SAME Q-minus-full-root component
as ANY chosen private basepoint. The selected-geometric witness
is required: general rooted extensions can have disconnected
private parts with identical root arities. -/
theorem selectedReplacementPiece_everyPrivate_connected
    (F : ∀ {W : Type}, Structure L W → Prop)
    {n : ℕ} (R : Structure L (Fin n))
    (Q : FunctionalRootExtension R)
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        R (Equiv.refl (Fin n)) Q) ∈
          forbiddenGeometricFunctionalPieces F n)
    (x : {q : Q.Carrier // q ∉ Set.range Q.rootEmbedding})
    (q : Q.Carrier) (hq : q ∉ Set.range Q.rootEmbedding) :
    q ∈ componentFrom Q.str.graph
      (Set.range Q.rootEmbedding) x := by
  classical
  let P := FunctionalRootExtension.toEnumeratedRootedPattern
    R (Equiv.refl (Fin n)) Q
  change IsForbiddenGeometricFunctionalPiece F P at hSelected
  obtain ⟨W, A, _hFinite, _hForbidden, d, ⟨e⟩⟩ := hSelected
  let G := geometricFunctionalRootedPattern A d
  let xG := functionalRootedIso_outsideRoot e x
  have hRootImage : e.equiv '' Set.range P.root = Set.range G.root :=
    functionalRootedIso_rootRange_image e
  have hQPrivate : e.equiv q ∉ Set.range G.root := by
    intro hIn
    rw [← hRootImage] at hIn
    obtain ⟨z, hz, heq⟩ := hIn
    have hzq : z = q := e.equiv.injective heq
    exact hq (hzq ▸ hz)
  have hG :
      e.equiv q ∈
        componentFrom G.str.graph (Set.range G.root) xG := by
    exact geometricSelectedPiece_everyPrivate_connected
      A d xG (e.equiv q) hQPrivate
  have hMap :
      e.equiv '' componentFrom P.str.graph
        (Set.range P.root) x =
      componentFrom G.str.graph (Set.range G.root) xG :=
    functionalRootedIso_component_image_eq e x
  have heImage :
      e.equiv q ∈
        e.equiv '' componentFrom P.str.graph
          (Set.range P.root) x := by
    rw [hMap]
    exact hG
  obtain ⟨z, hz, heq⟩ := heImage
  have hzq : z = q := e.equiv.injective heq
  exact hzq ▸ hz

/-- The SAME actual selected Q-private component both contains
every private Q vertex and has the COMPLETE generated functional
boundary equal to the full ordered root. The internal boundary
itself is not assumed; it is the already checked selected-geometric
boundary theorem (#805). -/
theorem selectedReplacementPiece_connectedPrivate_withGeneratedRoot
    (F : ∀ {W : Type}, Structure L W → Prop)
    {n : ℕ} (R : Structure L (Fin n))
    (Q : FunctionalRootExtension R)
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        R (Equiv.refl (Fin n)) Q) ∈
          forbiddenGeometricFunctionalPieces F n) :
    ∃ x : {q : Q.Carrier // q ∉ Set.range Q.rootEmbedding},
      (∀ q : Q.Carrier, q ∉ Set.range Q.rootEmbedding →
        q ∈ componentFrom Q.str.graph
          (Set.range Q.rootEmbedding) x) ∧
      Q.str.functionClosure
        (gaifmanNeighborhood Q.str.graph
          (componentFrom Q.str.graph
            (Set.range Q.rootEmbedding) x)) =
      Set.range Q.rootEmbedding := by
  obtain ⟨x, hBoundary⟩ :=
    selectedReplacementPiece_has_internalGeneratedRoot F R Q hSelected
  exact ⟨x,
    (fun q hq => selectedReplacementPiece_everyPrivate_connected
      F R Q hSelected x q hq),
    hBoundary⟩

end AllThoseRamseyClasses.Lifts
