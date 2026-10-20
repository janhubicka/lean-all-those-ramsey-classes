import AllThoseRamseyClasses.Lifts.GlobalMinimalMixedBoundaryCriterion

/-!
# Original global Claim 2 requires injective IMAGES of piece roots only

The earlier reduction assumed the original forbidden weak EHN map
was injective on the WHOLE preimage S of the common amalgam root.
That suffices but is stronger than the flip actually needs.

Here the source-geometric condition requires only that each
genuine minimal-separator root R ⊆ S be pairwise covered by FULL
irreducible tests of the forbidden source (these tests may extend
outside R). By EHN, the target map is injective on each such
enumerated root, even if it identifies other vertices of S.

Under this weaker source condition and the same explicit
two-boundary hypothesis for smallest mixed pieces, the complete
conditional Claim 2 minimality contradiction still works:
the initial genuine separator becomes mixed by Claim 1, select
a smallest mixed piece, produce a smaller genuine root via the
two-boundary lemma, and use Claim 1 again to force the smaller
piece mixed, contradicting minimality.

This does not establish the root-cover condition or the missing
boundary inclusions from the printed regularity/image-closure
assumptions. The unrestricted global Ramsey theorem remains open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every genuine source minimal-separator root lying inside S has
pairwise full irreducible-test coverage IN THE ORIGINAL SOURCE.
We do not demand injectivity on arbitrary pairs in S which cannot
occur together in any selected geometric piece root. -/
def GeometricPieceRootsPairwiseCoveredOn
    {V : Type}
    (Source : Structure L V) (S : Set V) : Prop :=
  ∀ {n : ℕ} (d : GeometricFunctionalPieceData Source n),
    Set.range d.roots ⊆ S →
    RootPairsCoveredByIrreducibleTests Source (Set.range d.roots)

/-- A source-attached piecewise coverage condition gives precisely
the target root-image injection needed by each occurrence of the
original global canonical flip, without making the whole weak map
injective on S or the ambient target. -/
theorem geometricRootImage_injective_of_piecewiseCover
    {V UT : Type}
    (Source : Structure L V)
    (S : Set V)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (hCover : GeometricPieceRootsPairwiseCoveredOn Source S)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (hRoots : Set.range d.roots ⊆ S) :
    Function.Injective (fun i : Fin n => f (d.roots i)) :=
  geometricRootImage_injective_of_pairwiseIrreducibleTestCover
    Source d Target f hf (hCover d hRoots)

/-- Under piecewise source-root coverage and the exact MINIMAL
mixed-piece two-boundary condition, no support-minimal forbidden
weak EHN witness can exist in the genuine original global-lift
free amalgam. The proof avoids any whole-S injectivity hypothesis. -/
theorem minimalGlobalForbiddenWitness_no_of_piecewiseCover_twoBoundaries
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
    (hBoundaries : MinimalMixedPieceTwoBoundaries w.source
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
  obtain ⟨a, haComp, haLeft⟩ := P.left_mixed
  obtain ⟨b, hbComp, hbRight⟩ := P.right_mixed
  let x : {v : w.Carrier // v ∉ S} := ⟨a, haLeft.2⟩
  let y : {v : w.Carrier // v ∉ S} := ⟨b, hbRight.2⟩
  have hSclosed : w.source.IsClosed S :=
    weakFreeRootPart_isClosed
      (sL := iLeft) (iL := jLeft)
      w.toTarget w.homEmbedding.1
  have hSepS : ¬ ReachOutside w.source.graph S x y :=
    weakFreePartition_root_separates_exclusive
      hTargetFree w.toTarget w.homEmbedding.1 haLeft hbRight
  have hBoundary :
      Set.range P.data.roots ⊆ w.source.functionClosure
        (gaifmanNeighborhood w.source.graph
          (componentFrom w.source.graph S x)) ∧
      Set.range P.data.roots ⊆ w.source.functionClosure
        (gaifmanNeighborhood w.source.graph
          (componentFrom w.source.graph S y)) :=
    hBoundaries P hPmin x y haComp haLeft hbComp hbRight
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
