import AllThoseRamseyClasses.Lifts.GeometricFunctionalPieces
import AllThoseRamseyClasses.Lifts.SeparatorPaths

/-!
# Components of a minimal geometric cut cannot reconnect through a larger cut

For an actual minimal functional separator R contained in another
vertex set S, any vertex z of the selected LEFT component C of A\R
cannot be connected to the selected RIGHT root y by a Gaifman path
which avoids S.

The proof is purely relational graph geometry using exact native
Gaifman paths and inclusions of the removed vertex sets.
Neither homomorphism-embedding, finiteness nor closure of the
larger set S is necessary. This is the reusable core of the
single-right-component case of the Section 3 lift argument:
a mixed selected piece can meet only an opposite-side component
DIFFERENT from the one chosen as the right separating root.

No global theorem that all opposite-side components are connected
is asserted.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A genuine minimal geometric piece with cut R ⊆ S cannot
contain any vertex reachable from its chosen opposite root
by a path avoiding the larger deleted set S.

In particular, every 'wrong-side' vertex in the selected piece
belongs to a different component of A minus S than its chosen
right-root vertex. -/
theorem minimalGeometricPiece_component_not_reachable_from_right
    (A : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData A n)
    (S : Set V)
    (hRS : Set.range d.roots ⊆ S)
    (y : {v : V // v ∉ S})
    (hy : d.right.1 = y.1)
    {z : V}
    (hzC : z ∈ functionalComponentFrom
      A (Set.range d.roots) d.left)
    (hzS : z ∉ S) :
    ¬ ReachOutside A.graph S y ⟨z, hzS⟩ := by
  intro hPath
  let R : Set V := Set.range d.roots
  let zS : {v : V // v ∉ S} := ⟨z, hzS⟩
  have hPathR :
      ReachOutside A.graph R
        (outsideCutMap hRS y) (outsideCutMap hRS zS) :=
    reachOutside_of_cut_subset A.graph hRS y zS hPath
  have hY : d.right = outsideCutMap hRS y := by
    apply Subtype.ext
    exact hy
  have hZ :
      (⟨z, hzC.1⟩ : {v : V // v ∉ R}) =
        outsideCutMap hRS zS := by
    apply Subtype.ext
    rfl
  have hRightZ :
      ReachOutside A.graph R
        d.right ⟨z, hzC.1⟩ := by
    rw [hY, hZ]
    exact hPathR
  have hLeftRight :
      ReachOutside A.graph R d.left d.right :=
    hzC.2.trans (reachOutside_symm A.graph R hRightZ)
  exact d.minimal.2.1 hLeftRight

end AllThoseRamseyClasses.Lifts
