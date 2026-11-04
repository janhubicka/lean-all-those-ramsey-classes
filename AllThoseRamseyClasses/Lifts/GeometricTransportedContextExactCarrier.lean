import AllThoseRamseyClasses.Lifts.FullFreeAmalgamExactTransportedContext
import AllThoseRamseyClasses.Lifts.GeometricOuterRootRetainedFullEmbedding
import AllThoseRamseyClasses.Lifts.GeometricRetainedInteriorPath

/-!
# Actual old geometric outer root and exact new contextual component

The generic full-functional context-carrier result is specialized
to a genuine OLD minimal-separator piece P, nested with a (possibly
INCOMPARABLE-cut) inner geometric piece d.

When the old outer root T survives deleting the old selected inner
component D, it has a CANONICAL closed preimage cut inside the
unchanged full complement E = Old \\ D:

  T_E = iOldE^{-1}(range(P.roots)).

Its full image in Old is EXACTLY the original closed root; no
enlarged generated hull, root renaming or weak target image is used.

The old component selected by P is literally the old-T component
anchored at P.left. Consequently the old context restriction
E intersect P is exactly the preimage of (old T union old component).

If the actual selected Q replacement has:
* full new-native free source gluing;
* full complement membership equivalence old/new across T_E;
* all Q-private vertices in one new old-root component;
* attachment of all surviving shared inner-root vertices;

then its entire transported outer context is EXACTLY the old ordered
root image plus ONE new outside-root component. This discharges the
CARRIER-EQUALITY premise of the verified global-symbol theorem,
without assuming that premise as a hypothesis.

No opposite function-generated boundary equation is proved here.
That remains Track A's independent necessary condition for a
genuine minimal-separator source piece. The source language remains
functional, with all arities and full output-value fibres.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The old outer geometric root survives as EXACTLY the full image
of a closed cut in the unchanged native functional inner complement.

The root's ordered vertices are still their original coordinates. -/
theorem geometricOuterRoot_exactClosedComplementCut
    {V : Type} (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Old
        (Set.range d.roots) d.left) :
    let E := geometricGlobalComplementChart Old d
    let iOldE : Structure.Embedding E.str Old :=
      functionalComponentComplementEmbedding Old
        (Set.range d.roots) d.minimal.1 d.left
    let T : Set E.Carrier := iOldE ⁻¹' Set.range P.roots
    E.str.IsClosed T ∧
    iOldE '' T = Set.range P.roots := by
  classical
  let E := geometricGlobalComplementChart Old d
  let iOldE : Structure.Embedding E.str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range d.roots) d.minimal.1 d.left
  let T : Set E.Carrier := iOldE ⁻¹' Set.range P.roots
  have hTclosed : E.str.IsClosed T :=
    functionalEmbedding_preimage_closed
      E.str Old iOldE (Set.range P.roots) P.minimal.1
  have hImage : iOldE '' T = Set.range P.roots := by
    apply Set.Subset.antisymm
    · rintro z ⟨b, hbT, hbz⟩
      exact hbz ▸ hbT
    · rintro z ⟨i, rfl⟩
      exact ⟨⟨P.roots i, hOuterRootOutside i⟩,
        ⟨i, rfl⟩, rfl⟩
  exact ⟨hTclosed, hImage⟩

/-- SOURCE-ATTACHED form of the exact transported context carrier
identity, with no abstract requirement that the old selected
context was a component union: its original geometric definition
provides that fact.

The new root is the literal ordered image of the OLD roots inside
the unchanged full complement, not a re-enumeration. We assume the
three smaller component facts tracked in the independent geometry
formalization; the ENTIRE context equality is proved. -/
theorem geometricTransportedContext_eq_root_union_newComponent
    {V W : Type}
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Old
        (Set.range d.roots) d.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old d).root)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iNewE : Structure.Embedding
      (geometricGlobalComplementChart Old d).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old d).rootEmbedding
      iQ iNewE)
    (xNew : {w : W // w ∉
      iNewE '' ((functionalComponentComplementEmbedding Old
        (Set.range d.roots) d.minimal.1 d.left) ⁻¹'
          Set.range P.roots)})
    (hRetained : ∀ b :
      (geometricGlobalComplementChart Old d).Carrier,
      b ∉ ((functionalComponentComplementEmbedding Old
        (Set.range d.roots) d.minimal.1 d.left) ⁻¹'
          Set.range P.roots) →
      ((functionalComponentComplementEmbedding Old
          (Set.range d.roots) d.minimal.1 d.left) b ∈
        componentFrom Old.graph (Set.range P.roots) P.left ↔
       iNewE b ∈ componentFrom New.graph
         (iNewE '' ((functionalComponentComplementEmbedding Old
           (Set.range d.roots) d.minimal.1 d.left) ⁻¹'
             Set.range P.roots)) xNew))
    (hQPrivate : ∀ q : Q.Carrier,
      q ∉ Set.range Q.rootEmbedding →
      iQ q ∈ componentFrom New.graph
        (iNewE '' ((functionalComponentComplementEmbedding Old
          (Set.range d.roots) d.minimal.1 d.left) ⁻¹'
            Set.range P.roots)) xNew)
    (hRootAttached : ∀ r : Fin m,
      (geometricGlobalComplementChart Old d).rootEmbedding r ∉
        ((functionalComponentComplementEmbedding Old
          (Set.range d.roots) d.minimal.1 d.left) ⁻¹'
            Set.range P.roots) →
      iNewE ((geometricGlobalComplementChart Old d).rootEmbedding r) ∈
        componentFrom New.graph
          (iNewE '' ((functionalComponentComplementEmbedding Old
            (Set.range d.roots) d.minimal.1 d.left) ⁻¹'
              Set.range P.roots)) xNew) :
    let roots : Fin n → W :=
      fun i => iNewE
        (⟨P.roots i, hOuterRootOutside i⟩ :
          (geometricGlobalComplementChart Old d).Carrier)
    ∃ x : {w : W // w ∉ Set.range roots},
      x.1 = xNew.1 ∧
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iNewE '' (oldOuterContextInInnerComplement Old P d)) =
        Set.range roots ∪
          componentFrom New.graph (Set.range roots) x := by
  classical
  let E := geometricGlobalComplementChart Old d
  let iOldE : Structure.Embedding E.str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range d.roots) d.minimal.1 d.left
  let T : Set E.Carrier := iOldE ⁻¹' Set.range P.roots
  obtain ⟨_hTclosed, hOldRootImage⟩ :=
    geometricOuterRoot_exactClosedComplementCut
      Old P d hOuterRootOutside
  let roots : Fin n → W :=
    fun i => iNewE
      (⟨P.roots i, hOuterRootOutside i⟩ : E.Carrier)
  have hNewRootImage : iNewE '' T = Set.range roots := by
    apply Set.Subset.antisymm
    · rintro z ⟨b, hbT, hbz⟩
      obtain ⟨i, hi⟩ := hbT
      have hbEq :
          b = (⟨P.roots i, hOuterRootOutside i⟩ : E.Carrier) := by
        apply Subtype.ext
        exact hi.symm
      refine ⟨i, ?_⟩
      exact (congrArg iNewE hbEq.symm).trans hbz
    · rintro z ⟨i, rfl⟩
      exact ⟨⟨P.roots i, hOuterRootOutside i⟩,
        ⟨i, rfl⟩, rfl⟩
  let xOld : {v : V // v ∉ iOldE '' T} :=
    ⟨P.left.1, by
      rw [hOldRootImage]
      exact P.left.2⟩
  have hOldCeq :
      componentFrom Old.graph (iOldE '' T) xOld =
        componentFrom Old.graph (Set.range P.roots) P.left :=
    sourceGaifmanComponent_eq_of_cut_eq
      Old hOldRootImage xOld P.left rfl
  have hPieceEq :
      geometricPieceVertices Old P =
        iOldE '' T ∪
          componentFrom Old.graph (iOldE '' T) xOld := by
    change (Set.range P.roots ∪
        componentFrom Old.graph (Set.range P.roots) P.left) = _
    exact (congrArg₂ (· ∪ ·) hOldRootImage.symm
      hOldCeq.symm)
  have hContextEq :
      oldOuterContextInInnerComplement Old P d =
        iOldE ⁻¹' (iOldE '' T ∪
          componentFrom Old.graph (iOldE '' T) xOld) := by
    change iOldE ⁻¹' geometricPieceVertices Old P = _
    rw [hPieceEq]
  have hRetained' : ∀ b : E.Carrier, b ∉ T →
      (iOldE b ∈ componentFrom Old.graph (iOldE '' T) xOld ↔
       iNewE b ∈ componentFrom New.graph (iNewE '' T) xNew) := by
    intro b hbT
    rw [hOldCeq]
    exact hRetained b hbT
  have hContext :
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iNewE '' (iOldE ⁻¹' (iOldE '' T ∪
          componentFrom Old.graph (iOldE '' T) xOld))) =
      iNewE '' T ∪
        componentFrom New.graph (iNewE '' T) xNew :=
    fullFreeAmalgam_transportedContext_eq_root_union_component
      hNewFree iOldE T xOld xNew
      hRetained' hQPrivate hRootAttached
  let x : {w : W // w ∉ Set.range roots} :=
    ⟨xNew.1, by
      rw [← hNewRootImage]
      exact xNew.2⟩
  have hComponentEq :
      componentFrom New.graph (iNewE '' T) xNew =
        componentFrom New.graph (Set.range roots) x :=
    sourceGaifmanComponent_eq_of_cut_eq
      New hNewRootImage xNew x rfl
  refine ⟨x, rfl, ?_⟩
  calc
    iQ '' (Set.univ : Set Q.Carrier) ∪
        iNewE '' (oldOuterContextInInnerComplement Old P d) =
      iQ '' (Set.univ : Set Q.Carrier) ∪
        iNewE '' (iOldE ⁻¹' (iOldE '' T ∪
          componentFrom Old.graph (iOldE '' T) xOld)) := by
            rw [hContextEq]
    _ = iNewE '' T ∪
          componentFrom New.graph (iNewE '' T) xNew := hContext
    _ = Set.range roots ∪
          componentFrom New.graph (Set.range roots) x := by
            rw [hNewRootImage, hComponentEq]

end AllThoseRamseyClasses.Lifts
