import AllThoseRamseyClasses.Lifts.RootRetentionLocalization

/-!
# Capture on one side can trap the opposite component inside the old piece

Let P be an actual outer geometric minimal closed separator, and
d a smaller genuine closed separator with its full root inside P
and its two distinguished source vertices inside P's selected
nonroot component. The standard Claim 2 smaller-root obstruction
occurs when d's selected (B) component captures vertices of P.root,
possibly escaping P.

If EVERY old P-root vertex belongs to d's selected B component,
then, by genuine separator disjointness, the opposite d.right
component captures NO old P-root vertex. Paths from d.right
avoid d's complete root and the old P-root, so its entire source
component stays in P's selected component. Together with d.root
inside P this gives a PROPER old-source subset on the OPPOSITE
side. The distinguished d.left source vertex witnesses strictness.

In particular, for old root width n=1, any captured old-root
vertex means that every old root is on d's selected B side,
hence the A-side opposite component is properly nested.
These are exact source geometry statements, not an opposite
A-to-B canonical flip or a terminal contradiction.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- When all old outer root SOURCE vertices are captured in the
selected d.left component, the OPPOSITE d.right component
cannot leave the original selected P component. Therefore the
closed new-root-plus-opposite-component source carrier is a
PROPER subset of the actual old P piece.

No weak map, target images, root width comparison or
A-purity of the opposite component is assumed. -/
theorem geometricPiece_oppositeProper_of_allOldRootsCaptured
    {V : Type}
    (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (d : GeometricFunctionalPieceData Source m)
    (hDrootInsideP :
      Set.range d.roots ⊆ geometricPieceVertices Source P)
    (hDleftOld :
      d.left.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left)
    (hDrightOld :
      d.right.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left)
    (hAllOldRootsCapturedLeft :
      Set.range P.roots ⊆
        functionalComponentFrom Source
          (Set.range d.roots) d.left) :
    functionalComponentFrom Source
        (Set.range d.roots) d.right ⊆
      functionalComponentFrom Source
        (Set.range P.roots) P.left ∧
    (Set.range d.roots ∪
        functionalComponentFrom Source
          (Set.range d.roots) d.right) ⊂
      geometricPieceVertices Source P := by
  classical
  have hDisjoint :=
    geometricPiece_components_disjoint Source d
  have hNoOldRootOnRight :
      ∀ r : V, r ∈ Set.range P.roots →
        r ∉ functionalComponentFrom Source
          (Set.range d.roots) d.right := by
    intro r hrOld hrRight
    exact (Set.disjoint_left.mp hDisjoint)
      (hAllOldRootsCapturedLeft hrOld) hrRight
  have hRightInsideOld :
      functionalComponentFrom Source
        (Set.range d.roots) d.right ⊆
      functionalComponentFrom Source
        (Set.range P.roots) P.left := by
    intro z hz
    have hLift :
        ∀ (v : {w : V // w ∉ Set.range d.roots}),
          ReachOutside Source.graph (Set.range d.roots) d.right v →
          v.1 ∈ functionalComponentFrom Source
            (Set.range P.roots) P.left := by
      intro v hPath
      induction hPath with
      | refl =>
          exact hDrightOld
      | @tail a b hab hedge ih =>
          have hbNew :
              b.1 ∈ functionalComponentFrom Source
                (Set.range d.roots) d.right :=
            ⟨b.2, hab.tail hedge⟩
          have hbNotOldRoot : b.1 ∉ Set.range P.roots := by
            intro hbOld
            exact hNoOldRootOnRight b.1 hbOld hbNew
          exact componentFrom_step Source.graph
            (Set.range P.roots) P.left ih hbNotOldRoot hedge
    exact hLift ⟨z, hz.1⟩ hz.2
  have hOppositeSubset :
      Set.range d.roots ∪
        functionalComponentFrom Source
          (Set.range d.roots) d.right ⊆
        geometricPieceVertices Source P := by
    intro z hz
    rcases hz with hzRoot | hzComp
    · exact hDrootInsideP hzRoot
    · exact Or.inr (hRightInsideOld hzComp)
  have hLeftInD :
      d.left.1 ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left :=
    componentFrom_root Source.graph (Set.range d.roots) d.left
  have hLeftNotOpposite :
      d.left.1 ∉
        (Set.range d.roots ∪
          functionalComponentFrom Source
            (Set.range d.roots) d.right) := by
    intro h
    rcases h with hRoot | hRight
    · exact d.left.2 hRoot
    · exact (Set.disjoint_left.mp hDisjoint) hLeftInD hRight
  have hProper :
      (Set.range d.roots ∪
        functionalComponentFrom Source
          (Set.range d.roots) d.right) ⊂
        geometricPieceVertices Source P := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨hOppositeSubset, ?_⟩
    intro hEq
    have hLeftOldPiece :
        d.left.1 ∈ geometricPieceVertices Source P :=
      Or.inr hDleftOld
    exact hLeftNotOpposite (hEq.symm ▸ hLeftOldPiece)
  exact ⟨hRightInsideOld, hProper⟩

/-- With a SINGLE old P-root vertex, capture by the smaller
selected B component automatically puts ALL old roots there.
The genuine OPPOSITE source carrier is therefore strictly
contained in P. This does not say that its A component is pure. -/
theorem geometricPiece_widthOne_capture_oppositeProper
    {V : Type}
    (Source : Structure L V)
    {m : ℕ}
    (P : GeometricFunctionalPieceData Source 1)
    (d : GeometricFunctionalPieceData Source m)
    (hDrootInsideP :
      Set.range d.roots ⊆ geometricPieceVertices Source P)
    (hDleftOld :
      d.left.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left)
    (hDrightOld :
      d.right.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left)
    (hCapture :
      ∃ r : V, r ∈ Set.range P.roots ∧
        r ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left) :
    functionalComponentFrom Source
        (Set.range d.roots) d.right ⊆
      functionalComponentFrom Source
        (Set.range P.roots) P.left ∧
    (Set.range d.roots ∪
        functionalComponentFrom Source
          (Set.range d.roots) d.right) ⊂
      geometricPieceVertices Source P := by
  obtain ⟨r, ⟨j, hj⟩, hCaptured⟩ := hCapture
  have hAllOldRootCaptured :
      Set.range P.roots ⊆
        functionalComponentFrom Source
          (Set.range d.roots) d.left := by
    rintro z ⟨i, hi⟩
    have hIndex : i = j := Subsingleton.elim i j
    have hz : z = r := by
      calc
        z = P.roots i := hi.symm
        _ = P.roots j := congrArg P.roots hIndex
        _ = r := hj
    simpa only [hz] using hCaptured
  exact geometricPiece_oppositeProper_of_allOldRootsCaptured
    Source P d hDrootInsideP hDleftOld hDrightOld
    hAllOldRootCaptured

end AllThoseRamseyClasses.Lifts
