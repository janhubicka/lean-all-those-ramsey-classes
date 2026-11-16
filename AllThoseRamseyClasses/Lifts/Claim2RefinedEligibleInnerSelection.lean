import AllThoseRamseyClasses.Lifts.Claim2PositiveRankEligibleInnerSelection
import AllThoseRamseyClasses.Lifts.Claim2AllWidthsPositiveRankFlip

/-!
# Track B: retain COMPLETE smaller-root source geometry in positive-rank trichotomy

The earlier Q-eligible-inner source selector retains a genuine
eligible B-only inner piece before choosing the selected Q, but
its two non-success alternatives project the selected smaller-root
witness down to a coarse CAPTURE or A-MIXED existential. This loses
essential B/A endpoint information needed by the verified all-width
original extremal source theorem.

The refined predicate below retains: genuine smaller positive-root
piece d, root inside old outer, both selected endpoints in the
original old component, complete d-root in full target seam,
injective ordered root targets, actual B-exclusive d.left,
A-exclusive d.right, and literal old-root capture/A-mixedness.

The new selection theorem reconstructs these certificates directly
from the SAME partner-versus-smaller native source geometry; no
new Q/source weak-map is selected, and the success branch remains
the original eligible inner geometric piece.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Genuine smaller-root obstruction retaining precisely the
SOURCE endpoints/root injection hypotheses needed by the verified
all-width original-global-A-minimum extremal lemma. It is strictly
MORE informative than bare old-root capture or A-mixedness. -/
def claim2NativeRefinedSmallerRootObstruction
    {F : ∀ {W : Type}, Structure L W → Prop}
    {UX UA UB UT : Type}
    {Target : Structure L UT}
    {Left : Structure L UA} {Right : Structure L UB}
    {jLeft : Structure.Embedding Left Target}
    {jRight : Structure.Embedding Right Target}
    {X : Structure L UX}
    {iLeft : Structure.Embedding X Left}
    {iRight : Structure.Embedding X Right}
    {n : ℕ}
    (s : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n) : Prop :=
  ∃ (m : ℕ) (d : GeometricFunctionalPieceData s.source m),
    0 < m ∧
    Set.range d.roots ⊆
      geometricPieceVertices s.source s.outer ∧
    d.left.1 ∈ functionalComponentFrom s.source
      (Set.range s.outer.roots) s.outer.left ∧
    d.right.1 ∈ functionalComponentFrom s.source
      (Set.range s.outer.roots) s.outer.left ∧
    Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) s.f ∧
    Function.Injective (fun i : Fin m => s.f (d.roots i)) ∧
    d.left.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) s.f ∧
    d.right.1 ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) s.f ∧
    ((∃ r : s.Carrier, r ∈ Set.range s.outer.roots ∧
        r ∈ functionalComponentFrom s.source
          (Set.range d.roots) d.left) ∨
     (∃ z : s.Carrier,
        z ∈ functionalComponentFrom s.source
          (Set.range d.roots) d.left ∧
        z ∈ weakFreeLeftPart
          (sL := iLeft) (iL := jLeft) s.f))

/-- The complete native source-geometric dichotomy, with no
premature erasure of the B/A smaller-root endpoint certificates.
The positive-rank successful branch is an actual eligible B-only
inner piece on which the SAME selected-Q theorem can operate. -/
theorem claim2Native_positiveRank_eligibleInner_or_refinedSmallerRoot
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    {n : ℕ}
    (s : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (hPositive : 0 < claim2NativeBSourceRank s) :
    claim2NativeEligibleInner s ∨
      claim2NativeRefinedSmallerRootObstruction s := by
  classical
  letI : Finite s.Carrier := s.finite
  let Source := s.source
  let f := s.f
  let P := s.outer
  let a := s.anchor
  let K : Set s.Carrier := geometricPieceVertices Source P
  let S : Set s.Carrier :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) f
  have hKclosed : Source.IsClosed K :=
    functionalComponentUnion_isClosed Source
      (Set.range P.roots) P.minimal.1 P.left
  have hNoEscape : FunctionalContextNoEscapeOutsideSeam Source S K :=
    geometricPiece_noEscapeOutsideContainingSeam
      Source P S s.outerRootInSeam
  obtain ⟨x, T, hxK, hxRight, hT, hTInside,
      y, hYa, hAlternative⟩ :=
    positiveLocalRightRank_noEscape_partner_or_smallerRoot
      F hConnected Source s.finite s.forbidden
      Target f s.hom Left Right jLeft jRight
      X iLeft iRight hFree
      K hKclosed hNoEscape a s.anchorInOuter s.anchorLeft hPositive
  have hTS : T ⊆ S := fun z hz => (hTInside hz).1
  have hxOuter : x.1 ∈ functionalComponentFrom Source
      (Set.range P.roots) P.left := by
    rcases hxK with hRoot | hComponent
    · obtain ⟨i, hi⟩ := hRoot
      have hxSeam : x.1 ∈ S :=
        hi ▸ s.outerRootInSeam ⟨i, rfl⟩
      exact False.elim (x.2 hxSeam)
    · exact hComponent
  have haOuter : a ∈ functionalComponentFrom Source
      (Set.range P.roots) P.left := by
    rcases s.anchorInOuter with hRoot | hComponent
    · obtain ⟨i, hi⟩ := hRoot
      have haSeam : a ∈ S := by
        have hRootSeam : P.roots i ∈ S :=
          s.outerRootInSeam ⟨i, rfl⟩
        change s.anchor ∈ S
        exact hi ▸ hRootSeam
      exact False.elim (s.anchorLeft.2 haSeam)
    · exact hComponent
  have hInjT : Set.InjOn f T := by
    rw [hT]
    exact s.activeBoundaryInj x hxK hxRight
  rcases hAlternative with hPartner |
      ⟨m, d, hm, hProper, hRootIn, hLeft, hRight, hExactRoot⟩
  · -- Matching exact opposite boundary: construct an eligible d first.
    have hSclosed : Source.IsClosed S :=
      weakFreeRootPart_isClosed
        (sL := iLeft) (iL := jLeft) f s.hom.1
    have hBNoA :
        ∀ z : s.Carrier,
          z ∈ componentFrom Source.graph S x →
          z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f := by
      intro z hz hzA
      have hzB : z ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f :=
        weakFreePartition_component_right
          hFree f s.hom.1 x hxRight hz
      exact (Set.disjoint_left.mp
        (weakFreePartition_left_right_disjoint hFree f)) hzA hzB
    have haNotComponent : a ∉ componentFrom Source.graph S x := by
      intro haComp
      exact hBNoA a haComp s.anchorLeft
    have hConnectedPath : ReachOutside Source.graph (∅ : Set s.Carrier)
        (⟨x.1, by simp⟩ : {v : s.Carrier // v ∉ ∅})
        (⟨a, by simp⟩ : {v : s.Carrier // v ∉ ∅}) :=
      gaifmanPath_to_emptyCutReach Source
        ((hConnected Source s.finite s.forbidden).2 x.1 a)
    have hTnonempty : T.Nonempty := by
      rw [hT]
      exact functionalComponent_generatedBoundary_nonempty_of_emptyCutReach
        Source S x a haNotComponent hConnectedPath
    obtain ⟨y', hy'Val, hSeparated'⟩ :=
      weakRightComponent_leftVertex_separatedByBoundary
        hFree f s.hom x hxRight T hT hTS a s.anchorLeft
    have hYeq : y' = y := Subtype.ext (hy'Val.trans hYa.symm)
    have hSeparated : ¬ ReachOutside Source.graph T
        (outsideCutMap hTS x) y := by
      simpa only [hYeq] using hSeparated'
    obtain ⟨m, d, hm, _hDRoot, hDRootInside,
        hDproper, hDComp, hNoA, hRootInj⟩ :=
      geometricPiece_properInnerOneSided_of_boundaryPartner
        Source P S hSclosed s.outerRootInSeam
        x hxOuter
        (weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
        hBNoA a haOuter s.anchorLeft.2 s.anchorLeft
        T hT hTS hTnonempty y hSeparated hPartner
        f hInjT
    have hRootSeam : Set.range d.roots ⊆ S := by
      intro z hz
      exact (hDRootInside hz).1
    have hOuterRootOutside : ∀ i : Fin n,
        P.roots i ∉ functionalComponentFrom Source
          (Set.range d.roots) d.left := by
      intro i hi
      have hiB : P.roots i ∈ componentFrom Source.graph S x := by
        simpa only [hDComp] using hi
      exact hiB.1 (s.outerRootInSeam ⟨i, rfl⟩)
    have hxD : x.1 ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left := by
      change x.1 ∈ componentFrom Source.graph
        (Set.range d.roots) d.left
      rw [hDComp]
      exact componentFrom_root Source.graph S x
    exact Or.inl
      ⟨m, d, hm, hDproper.subset, hOuterRootOutside,
        hRootSeam, hNoA, hRootInj, x.1, hxD, hxRight⟩
  · -- The smaller root d is real, but might capture an OLD root or
    -- contain an A-only vertex. Only the remaining case is eligible.
    have hRootInSeam : Set.range d.roots ⊆ S :=
      fun z hz => (hRootIn hz).1
    have hRootInOuter : Set.range d.roots ⊆ K :=
      fun z hz => (hRootIn hz).2
    have hdLeftOld : d.left.1 ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left := by
      rw [hLeft]
      exact hxOuter
    have hDrootInj :
        Function.Injective (fun i : Fin m => f (d.roots i)) := by
      intro i j hij
      apply d.roots_injective
      exact hInjT
        (hProper.subset ⟨i, rfl⟩)
        (hProper.subset ⟨j, rfl⟩) hij
    have hdRightOld : d.right.1 ∈
        functionalComponentFrom Source
          (Set.range P.roots) P.left := by
      rw [hRight]
      exact haOuter
    have hdLeftB : d.left.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f := by
      rw [hLeft]
      exact hxRight
    have hdRightA : d.right.1 ∈ weakFreeLeftPart
        (sL := iLeft) (iL := jLeft) f := by
      rw [hRight]
      exact s.anchorLeft
    by_cases hCapture :
        ∃ i : Fin n, P.roots i ∈
          functionalComponentFrom Source (Set.range d.roots) d.left
    · obtain ⟨i, hCaptured⟩ := hCapture
      exact Or.inr
        ⟨m, d, hm, hRootInOuter, hdLeftOld, hdRightOld,
          hRootInSeam, hDrootInj, hdLeftB, hdRightA,
          Or.inl ⟨P.roots i, ⟨i, rfl⟩, hCaptured⟩⟩
    · by_cases hMixed :
          ∃ z : s.Carrier,
            z ∈ functionalComponentFrom Source
              (Set.range d.roots) d.left ∧
            z ∈ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f
      · exact Or.inr
          ⟨m, d, hm, hRootInOuter, hdLeftOld, hdRightOld,
            hRootInSeam, hDrootInj, hdLeftB, hdRightA,
            Or.inr hMixed⟩
      · have hNoCapture : ∀ r : s.Carrier,
            r ∈ Set.range P.roots →
            r ∉ functionalComponentFrom Source
              (Set.range d.roots) d.left := by
          intro r hr hrc
          obtain ⟨i, hi⟩ := hr
          exact hCapture ⟨i, hi.symm ▸ hrc⟩
        have hNoA : ∀ z : s.Carrier,
            z ∈ functionalComponentFrom Source
              (Set.range d.roots) d.left →
            z ∉ weakFreeLeftPart
              (sL := iLeft) (iL := jLeft) f := by
          intro z hz hzA
          exact hMixed ⟨z, hz, hzA⟩
        have hDcomponentInsideP :
            functionalComponentFrom Source
              (Set.range d.roots) d.left ⊆
            functionalComponentFrom Source
              (Set.range P.roots) P.left := by
          by_contra hEscape
          obtain ⟨r, hrOldRoot, hrCaptured⟩ :=
            geometricPiece_escapingComponent_capturesOldRoot
              Source P d hdLeftOld hEscape
          exact hNoCapture r hrOldRoot hrCaptured
        have hInnerInside :
            geometricPieceVertices Source d ⊆
              geometricPieceVertices Source P := by
          intro z hz
          rcases hz with hzRoot | hzComp
          · exact hRootInOuter hzRoot
          · exact Or.inr (hDcomponentInsideP hzComp)
        have hOuterRootOutside : ∀ i : Fin n,
            P.roots i ∉ functionalComponentFrom Source
              (Set.range d.roots) d.left := by
          intro i
          exact hNoCapture (P.roots i) ⟨i, rfl⟩
        have hxD : d.left.1 ∈
            functionalComponentFrom Source
              (Set.range d.roots) d.left :=
          componentFrom_root Source.graph (Set.range d.roots) d.left
        have hdB : d.left.1 ∈ weakFreeRightPart
            (sL := iLeft) (iL := jLeft) (iR := jRight) f := by
          rw [hLeft]
          exact hxRight
        exact Or.inl
          ⟨m, d, hm, hInnerInside, hOuterRootOutside,
            hRootInSeam, hNoA, hDrootInj,
            d.left.1, hxD, hdB⟩


end AllThoseRamseyClasses.Lifts
