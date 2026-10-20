import AllThoseRamseyClasses.Lifts.GlobalPiecewiseRootCoverageCriterion

/-!
# A selected opposite-side pair suffices for the actual Claim 2 descent

The earlier conditional Section 3 proof assumes that for EVERY
opposite-colour pair in EVERY globally smallest genuinely mixed
forbidden-source piece, the original piece root lies in both
generated component-neighborhood closures after deleting the
common amalgam-root preimage.

The already verified minimality contradiction uses precisely ONE
such pair. This module isolates that strictly weaker, existential
source-geometric condition, with the SAME native functions, actual
minimal closed separator pieces, and root-image injectivity supplied
by EHN coverage only on genuine piece roots.

Both this hypothesis and the root-coverage hypothesis remain
unproved for general connected regular image-closed forbidden
families. They are explicit proof obligations, not hidden axioms
or a certification of the unrestricted 2019 theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An ACTUAL smallest mixed geometric source piece has SOME
opposite-colour vertices x and y of its selected component
such that the closed piece root is contained in the generated
neighborhood closures of the x- and y-components after deleting S.

This asks for one appropriately chosen pair, not every pair.
The names AOnly/BOnly refer to source vertices, not target maps. -/
def MinimalMixedPieceSelectedBoundaries
    {V : Type}
    (Source : Structure L V) (S AOnly BOnly : Set V) : Prop :=
  ∀ (P : MixedGeometricPiece Source S AOnly BOnly)
    (hMinimal : ∀ Q : MixedGeometricPiece Source S AOnly BOnly,
      P.nonrootCount ≤ Q.nonrootCount),
    ∃ (x y : {v : V // v ∉ S}),
      x.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left ∧
      x.1 ∈ AOnly ∧
      y.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left ∧
      y.1 ∈ BOnly ∧
      (Set.range P.data.roots ⊆ Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph S x))) ∧
      (Set.range P.data.roots ⊆ Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph S y)))

/-- The old universal two-boundary assumption implies the
weaker selected-pair assumption whenever exclusive colour sets
do not intersect the deleted common-root set. -/
theorem minimalMixedPieceSelectedBoundaries_of_allPairs
    {V : Type}
    (Source : Structure L V)
    (S AOnly BOnly : Set V)
    (hA : ∀ {x : V}, x ∈ AOnly → x ∉ S)
    (hB : ∀ {y : V}, y ∈ BOnly → y ∉ S)
    (hEvery : MinimalMixedPieceTwoBoundaries Source S AOnly BOnly) :
    MinimalMixedPieceSelectedBoundaries Source S AOnly BOnly := by
  intro P hMinimal
  obtain ⟨a, haComp, haA⟩ := P.left_mixed
  obtain ⟨b, hbComp, hbB⟩ := P.right_mixed
  let x : {v : V // v ∉ S} := ⟨a, hA haA⟩
  let y : {v : V // v ∉ S} := ⟨b, hB hbB⟩
  refine ⟨x, y, haComp, haA, hbComp, hbB, ?_, ?_⟩
  · exact (hEvery P hMinimal x y haComp haA hbComp hbB).1
  · exact (hEvery P hMinimal x y haComp haA hbComp hbB).2

/-- A support-minimal forbidden EHN witness contradicts its own
minimal mixed-piece cardinality under only the SELECTED-pair
boundary condition and coverage of real geometric roots.

No source-to-target map is injected globally or on the whole
common-root preimage. The two hypotheses remain explicit. -/
theorem minimalGlobalForbiddenWitness_no_of_piecewiseCover_selectedBoundaries
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (hAvoidLeft : AvoidsGlobalFunctionalEHN F Left)
    (hAvoidRight : AvoidsGlobalFunctionalEHN F Right)
    (w : ForbiddenEHNWitness F Target)
    (hMin : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft))
    (hPieceCover : GeometricPieceRootsPairwiseCoveredOn w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget))
    (hSelected : MinimalMixedPieceSelectedBoundaries w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)) :
    False := by
  let S : Set w.Carrier :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget
  let AOnly : Set w.Carrier :=
    weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget
  let BOnly : Set w.Carrier :=
    weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget
  letI : Finite w.Carrier := w.finiteCarrier
  obtain ⟨n, d, hn, hRoots, hLeft, _hRight, _hPiece, hCases⟩ :=
    minimalGlobalForbiddenWitness_collidingRoot_or_mixedPiece
      F hFiniteF hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hTargetFree hCommon hAvoidLeft hAvoidRight w hMin
  have hDinj : Function.Injective
      (fun i : Fin n => w.toTarget (d.roots i)) :=
    geometricRootImage_injective_of_piecewiseCover
      w.source S Target w.toTarget w.homEmbedding
      hPieceCover d hRoots
  have hMixedRight :
      ∃ z : w.Carrier,
        z ∈ functionalComponentFrom w.source
          (Set.range d.roots) d.left ∧ z ∈ BOnly := by
    rcases hCases with hCollision | hRight
    · exact False.elim (hCollision hDinj)
    · exact hRight
  let P0 : MixedGeometricPiece w.source S AOnly BOnly := {
    width := n
    data := d
    positive := hn
    roots_in_common := hRoots
    left_mixed := ⟨d.left.1,
      functionalComponentFrom_root w.source (Set.range d.roots) d.left,
      hLeft⟩
    right_mixed := hMixedRight
  }
  obtain ⟨P, hPmin⟩ :=
    exists_minimalMixedGeometricPiece w.source S AOnly BOnly ⟨P0⟩
  obtain ⟨x, y, haComp, haLeft, hbComp, hbRight, hBoundary⟩ :=
    hSelected P hPmin
  have hSclosed : w.source.IsClosed S :=
    weakFreeRootPart_isClosed
      (sL := iLeft) (iL := jLeft)
      w.toTarget w.homEmbedding.1
  have hSepS : ¬ ReachOutside w.source.graph S x y :=
    weakFreePartition_root_separates_exclusive
      hTargetFree w.toTarget w.homEmbedding.1 haLeft hbRight
  obtain ⟨m, Q, hGrow, hQrootS, hQleft, _hQright,
      _hCompProper, hCompCount⟩ :=
    finite_geometricPiece_strictComponentDescent_of_boundaries
      w.source P.data S hSclosed P.roots_in_common
      x y haComp hbComp hSepS hBoundary
  have hmPos : 0 < m := by
    by_contra hNotPos
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hNotPos
    subst m
    let i : Fin P.width := ⟨0, P.positive⟩
    obtain ⟨j, _hj⟩ :=
      hGrow.subset (show P.data.roots i ∈ Set.range P.data.roots
        from ⟨i, rfl⟩)
    exact Fin.elim0 j
  have hQleft : Q.left.1 ∈ AOnly := by
    rw [hQleft]
    exact haLeft
  have hQinj : Function.Injective
      (fun i : Fin m => w.toTarget (Q.roots i)) :=
    geometricRootImage_injective_of_piecewiseCover
      w.source S Target w.toTarget w.homEmbedding
      hPieceCover Q hQrootS
  have hQright :
      ∃ z : w.Carrier,
        z ∈ functionalComponentFrom w.source
          (Set.range Q.roots) Q.left ∧ z ∈ BOnly :=
    minimalGlobalWitness_pieceMeetsRight_of_rootInjective
      F hFiniteF Target Left Right jLeft jRight
      X iLeft iRight hTargetFree hCommon w hMin
      Q hmPos hQrootS hQleft hQinj
  let QMixed : MixedGeometricPiece w.source S AOnly BOnly := {
    width := m
    data := Q
    positive := hmPos
    roots_in_common := hQrootS
    left_mixed := ⟨Q.left.1,
      functionalComponentFrom_root w.source
        (Set.range Q.roots) Q.left, hQleft⟩
    right_mixed := hQright
  }
  have hCount :
      QMixed.nonrootCount < P.nonrootCount := hCompCount
  exact (Nat.not_lt_of_ge (hPmin QMixed)) hCount

end AllThoseRamseyClasses.Lifts
