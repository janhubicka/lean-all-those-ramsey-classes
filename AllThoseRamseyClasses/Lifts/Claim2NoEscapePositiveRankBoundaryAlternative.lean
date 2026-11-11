import AllThoseRamseyClasses.Lifts.Claim2PositiveRankNoEscapeComponent
import AllThoseRamseyClasses.Lifts.Claim2BoundaryPartnerOrSmallerRoot
import AllThoseRamseyClasses.Lifts.WeakRightBoundarySeparation
import AllThoseRamseyClasses.Lifts.ConnectedForbiddenPositivePiece

/-!
# Track C: partner-or-smaller positive root inside a NON-GEOMETRIC no-escape context

The source boundary alternative of the original Claim 2 was
previously formulated for an old outer GEOMETRIC minimal-cut piece.
Successful B-to-A replacements, however, are only known to
transport a function-closed, no-escape contextual carrier K.

The actual source-geometric boundary proof requires much less:
for any closed seam S and chosen S-component B starting in such
a K, its complete generated boundary T=Cl(N(B)) lies in S∩K.
For any y in a different T-component, its full generated
opposite boundary U is contained in T. Either U=T, providing
a genuine matching boundary partner, OR U is a strictly smaller
source MINIMAL closed separator with ordered root contained
in S∩K. If x and y are connected in the whole source, this
new root is POSITIVE-width.

We compose that dichotomy with the full native free-amalgam
monochromaticity theorem and with the *actual* positive
B-exclusive SOURCE-count witness selector. In any finite
CONNECTED forbidden source, a positive B-rank in K and a
single A-exclusive source anchor a in K supply x, the exact
boundary T, the opposite vertex y=a, its separation, and the
exhaustive partner / positive smaller-root alternative.

No intermediate left-support minimality, geometric minimality
of K, global injectivity of a weak EHN map, or arbitrary
source-image quotient is assumed.

The remaining genuine mathematical obstruction is still
the mixed selected component after shrinking a root, plus
possible root-image collisions. The new theorem DOES NOT
assert either branch is automatically flippable, nor does
it produce the terminal genuine selected geometric piece.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- For arbitrary source closed/no-escape K and closed S, an
S-component's complete generated boundary T either has the
required matching opposite partner or a STRICTLY smaller
POSITIVE-width genuine minimal closed separator root U,
entirely inside S∩K, provided the selected x,y vertices
are connected in the whole native Gaifman source. -/
theorem noEscapeComponent_partner_or_smallerPositiveRoot
    {V : Type} [Finite V]
    (Source : Structure L V)
    (S K : Set V)
    (hSclosed : Source.IsClosed S)
    (hKclosed : Source.IsClosed K)
    (hNoEscape : FunctionalContextNoEscapeOutsideSeam Source S K)
    (x : {v : V // v ∉ S}) (hxK : x.1 ∈ K)
    (T : Set V)
    (hT : T = Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph S x)))
    (hTS : T ⊆ S)
    (y : {v : V // v ∉ T})
    (hSeparated : ¬ ReachOutside Source.graph T
      (outsideCutMap hTS x) y)
    (hConnected : ReachOutside Source.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {v : V // v ∉ ∅})
      (⟨y.1, by simp⟩ : {v : V // v ∉ ∅})) :
    (Source.functionClosure
       (gaifmanNeighborhood Source.graph
         (componentFrom Source.graph T y)) = T) ∨
      (∃ (m : ℕ) (d : GeometricFunctionalPieceData Source m),
        0 < m ∧
        Set.range d.roots ⊂ T ∧
        Set.range d.roots ⊆ S ∩ K ∧
        d.left.1 = x.1 ∧ d.right.1 = y.1 ∧
        Set.range d.roots =
          Source.functionClosure
            (gaifmanNeighborhood Source.graph
              (componentFrom Source.graph T y))) := by
  classical
  let U : Set V :=
    Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph T y))
  let xT : {v : V // v ∉ T} := outsideCutMap hTS x
  have hTclosed : Source.IsClosed T := by
    rw [hT]
    exact Source.functionClosure_isClosed _
  have hCsame :
      componentFrom Source.graph T xT =
        componentFrom Source.graph S x := by
    cases hT
    exact componentBoundaryClosure_preserves_exact_component
      Source S hSclosed x
  have hFullX :
      Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph T xT)) = T := by
    rw [hCsame]
    exact hT.symm
  have hUT : U ⊆ T :=
    functionalClosure_neighborhood_subset_cut
      Source T hTclosed y
  by_cases hPartner : U = T
  · exact Or.inl hPartner
  · right
    have hProper : U ⊂ T :=
      Set.ssubset_iff_subset_ne.mpr ⟨hUT, hPartner⟩
    have hMin : IsMinimalClosedSeparator Source U
        (outsideCutMap hUT xT) (outsideCutMap hUT y) :=
      oppositeBoundaryClosure_isMinimalClosedSeparator
        Source T hTclosed xT y hSeparated hFullX
    obtain ⟨m, d, hRoot, hLeft, hRight⟩ :=
      finiteMinimalClosedSeparator_toGeometricChart
        Source U (outsideCutMap hUT xT)
        (outsideCutMap hUT y) hMin
    have hTInside : T ⊆ S ∩ K := by
      intro z hz
      exact functionalNoEscape_component_generatedBoundary_inside
        Source S K hSclosed hKclosed hNoEscape x hxK
        (by simpa only [hT] using hz)
    have hRootInside :
        Set.range d.roots ⊆ S ∩ K := by
      intro z hz
      exact hTInside (hUT (by simpa only [hRoot] using hz))
    have hConnectedD : ReachOutside Source.graph (∅ : Set V)
        (⟨d.left.1, by simp⟩ : {v : V // v ∉ ∅})
        (⟨d.right.1, by simp⟩ : {v : V // v ∉ ∅}) := by
      have hLeftVal : d.left.1 = x.1 := by
        change d.left.1 = x.1 at hLeft
        exact hLeft
      have hRightVal : d.right.1 = y.1 := by
        simpa only [outsideCutMap] using hRight
      simpa only [hLeftVal, hRightVal] using hConnected
    have hNonempty : (Set.range d.roots).Nonempty :=
      minimalClosedSeparator_nonempty_of_emptyCut_path
        Source (Set.range d.roots) d.left d.right
        d.minimal hConnectedD
    obtain ⟨z, hz⟩ := hNonempty
    obtain ⟨i, _hi⟩ := hz
    have hm : 0 < m := by
      cases m with
      | zero => exact Fin.elim0 i
      | succ k => exact Nat.zero_lt_succ k
    exact ⟨m, d, hm, by simpa only [hRoot] using hProper,
      hRootInside, hLeft, hRight, hRoot⟩

/-- Every actual finite connected forbidden source with a
positive B-exclusive SOURCE rank inside ANY closed no-escape K
and a surviving A-exclusive source anchor a in that same K
exhibits a fully grounded native boundary alternative:
a true opposite A-component partner to the chosen B-component,
or an explicitly smaller positive-width geometric source root
inside S∩K.

The x component and generated T are determined by the
positive source count, the source path comes from the
original forbidden family's connectedness, and y is the
literal A-only source vertex a. No outer geometric P needed. -/
theorem positiveLocalRightRank_noEscape_partner_or_smallerRoot
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V) (hForbidden : F Source)
    (Target : Structure L UT) (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (K : Set V) (hKclosed : Source.IsClosed K)
    (hNoEscape : FunctionalContextNoEscapeOutsideSeam Source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) K)
    (a : V) (haK : a ∈ K)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (hPositiveB :
      0 < Nat.card {v : V //
        v ∈ K ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight}) :
    ∃ (x : {v : V //
        v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
      (T : Set V),
      x.1 ∈ K ∧
      x.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f ∧
      T = Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)) ∧
      T ⊆
        weakFreeRootPart (sL := iLeft) (iL := jLeft) f ∩ K ∧
      ∃ (y : {v : V // v ∉ T}),
        y.1 = a ∧
        (Source.functionClosure
           (gaifmanNeighborhood Source.graph
             (componentFrom Source.graph T y)) = T ∨
         ∃ (m : ℕ) (d : GeometricFunctionalPieceData Source m),
           0 < m ∧
           Set.range d.roots ⊂ T ∧
           Set.range d.roots ⊆
             weakFreeRootPart (sL := iLeft) (iL := jLeft) f ∩ K ∧
           d.left.1 = x.1 ∧ d.right.1 = a ∧
           Set.range d.roots =
             Source.functionClosure
               (gaifmanNeighborhood Source.graph
                 (componentFrom Source.graph T y))) := by
  classical
  letI : Finite V := hFinite
  let S : Set V :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) f
  obtain ⟨x, T, hxK, hxRight, _hCompInside,
      _hCompRight, hT, hTInside⟩ :=
    positiveLocalRightSupport_noEscape_hasInnerComponent
      Source hFinite Target f hf
      Left Right jLeft jRight X iLeft iRight
      hFree K hKclosed hNoEscape hPositiveB
  have hSclosed : Source.IsClosed S :=
    weakFreeRootPart_isClosed
      (sL := iLeft) (iL := jLeft) f hf.1
  have hTS : T ⊆ S := fun z hz => (hTInside hz).1
  obtain ⟨y, hYa, hSep⟩ :=
    weakRightComponent_leftVertex_separatedByBoundary
      hFree f hf x hxRight T hT hTS a haLeft
  have hPathY : ReachOutside Source.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {v : V // v ∉ ∅})
      (⟨y.1, by simp⟩ : {v : V // v ∉ ∅}) := by
    have hPathA : ReachOutside Source.graph (∅ : Set V)
        (⟨x.1, by simp⟩ : {v : V // v ∉ ∅})
        (⟨a, by simp⟩ : {v : V // v ∉ ∅}) :=
      gaifmanPath_to_emptyCutReach Source
        ((hConnected Source hFinite hForbidden).2 x.1 a)
    simpa only [hYa] using hPathA
  rcases noEscapeComponent_partner_or_smallerPositiveRoot
      Source S K hSclosed hKclosed hNoEscape
      x hxK T hT hTS y hSep hPathY with
    hPartner | ⟨m, d, hm, hProper, hRootIn, hLeft, hRight, hBoundary⟩
  · exact ⟨x, T, hxK, hxRight, hT, hTInside,
      y, hYa, Or.inl hPartner⟩
  · exact ⟨x, T, hxK, hxRight, hT, hTInside,
      y, hYa, Or.inr
        ⟨m, d, hm, hProper, hRootIn,
          hLeft, hRight.trans hYa, hBoundary⟩⟩

end AllThoseRamseyClasses.Lifts
