import AllThoseRamseyClasses.Lifts.GlobalMinimalMixedPieceFromRootInjOn
import AllThoseRamseyClasses.Lifts.Claim2ConditionalLargerGeometricPiece
import AllThoseRamseyClasses.Lifts.GlobalRootPairwiseTestCoverage

/-!
# Exact remaining source-boundary condition for original Section 3 Claim 2

The verified original-global Claim 1 excludes every one-sided
positive-width geometric source piece rooted in the common full seam
whose ordered TARGET root images are injective.

The new conditional larger-root lemma constructs a genuine source
piece Q with STRICTLY FEWER nonroot vertices than a chosen mixed
piece P, assuming the root of P is contained in both generated
neighborhood closures of selected opposite-side components after
deleting the common-root preimage S.

If the weak map is injective ON S, the new Q has an injective root
image, so the verified Claim 1 forces Q itself to be mixed. This
contradicts the minimality of P. Hence the original support-minimal
forbidden obstruction is impossible under the exact missing
two-boundary condition.

This packages the printed Claim 2 into ONE explicit geometric
hypothesis on minimal mixed pieces, separate from the root-collision
hypothesis. It does not claim either hypothesis in the unrestricted
regular, image-closed forbidden-family setting. The full theorem
remains open until they are established or the proof is repaired.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The precise unverified TWO-BOUNDARY implication needed for
the actual Section 3 minimal-mixed-piece argument. A minimal
genuinely mixed source piece P with root R is given, and x,y
are arbitrary opposite-exclusive vertices in its selected
nonroot component. The condition asks R to lie in BOTH full
functional neighborhood closures of their components after
deleting S, the complete common-root preimage.

This condition is NOT inferred from minimality or the mere
fact that P is mixed. It names an outstanding mathematical
proof obligation rather than an opaque strong-AP hypothesis. -/
def MinimalMixedPieceTwoBoundaries
    {V : Type}
    (Source : Structure L V) (S AOnly BOnly : Set V) : Prop :=
  ∀ (P : MixedGeometricPiece Source S AOnly BOnly)
    (hMinimal : ∀ Q : MixedGeometricPiece Source S AOnly BOnly,
      P.nonrootCount ≤ Q.nonrootCount)
    (x y : {v : V // v ∉ S}),
    x.1 ∈ functionalComponentFrom Source
      (Set.range P.data.roots) P.data.left →
    x.1 ∈ AOnly →
    y.1 ∈ functionalComponentFrom Source
      (Set.range P.data.roots) P.data.left →
    y.1 ∈ BOnly →
    (Set.range P.data.roots ⊆ Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph S x))) ∧
    (Set.range P.data.roots ⊆ Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph S y)))

/-- If the target map is injective ON THE COMMON-ROOT PREIMAGE
and the precise two-boundary condition holds for minimal mixed
pieces, there can be NO support-minimal forbidden EHN witness
in the native full free amalgam of two forbidden-free sides
with matching full original canonical lifts.

The proof uses actual finite source minimization, genuine
minimal-cut geometric pieces, the verified one-sided Claim 1
flip, and the strict nonroot cardinality from a newly selected
closed separator. The missing boundary condition and root
injectivity are not silently discharged. -/
theorem minimalGlobalForbiddenWitness_no_of_rootInjOn_twoBoundaries
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
    (hRootInjOn : Set.InjOn w.toTarget
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
  obtain ⟨P, hPmin⟩ :=
    minimalGlobalForbiddenWitness_exists_minimalMixedPiece_of_rootInjOn
      F hFiniteF hConnected Target Left Right jLeft jRight
      X iLeft iRight hTargetFree hCommon hAvoidLeft hAvoidRight
      w hMin hRootInjOn
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
      (fun i : Fin m => w.toTarget (Q.roots i)) := by
    intro i j hij
    apply Q.roots_injective
    exact hRootInjOn
      (hQrootS ⟨i, rfl⟩) (hQrootS ⟨j, rfl⟩) hij
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

/-- A SOURCE-side sufficient condition for the same contradiction:
pairwise coverage of the common-root preimage by irreducible full
source tests makes its weak EHN map injective there.

This is still conditional on both source-geometric assumptions;
it does NOT prove either for arbitrary forbidden families. -/
theorem minimalGlobalForbiddenWitness_no_of_pairCover_twoBoundaries
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
    (hPairCover : RootPairsCoveredByIrreducibleTests w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget))
    (hBoundaries : MinimalMixedPieceTwoBoundaries w.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
      (weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)) :
    False := by
  exact minimalGlobalForbiddenWitness_no_of_rootInjOn_twoBoundaries
    F hFiniteF hConnected
    Target Left Right jLeft jRight X iLeft iRight
    hTargetFree hCommon hAvoidLeft hAvoidRight w hMin
    (ehn_injOn_of_rootPairsCoveredByIrreducibleTests
      w.source Target w.toTarget w.homEmbedding
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
      hPairCover)
    hBoundaries

end AllThoseRamseyClasses.Lifts
