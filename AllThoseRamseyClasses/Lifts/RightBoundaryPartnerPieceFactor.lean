import AllThoseRamseyClasses.Lifts.ComponentBoundaryPieceCriterion
import AllThoseRamseyClasses.Lifts.GeometricPieceRightFactor
import AllThoseRamseyClasses.Lifts.GlobalPiecewiseRootCoverageCriterion
import AllThoseRamseyClasses.Lifts.PositiveGeometricRootFromConnectedPath

/-!
# One actual right-exclusive component yields a full EHN piece under a boundary partner

This combines three separately verified ingredients of the
original Section 3 lift construction:

1. A finite source component C outside the common full root
   preimage S, with T = Cl(N(C)), has a GENUINE minimal closed
   separator piece rooted at T whenever a second component of
   Source minus T is separated from C and has boundary closure T.
2. This piece's selected nonroot component is EXACTLY C. Since
   C contains a right-exclusive source vertex, it contains
   no left-exclusive source vertex in a functional free amalgam.
   The verified right factorization therefore constructs a
   real EHN homomorphism-embedding of the whole piece into Right.
3. If the chosen piece root is pairwise covered by full
   irreducible source tests, its ordered TARGET images are
   injective. If the selected vertices are connected in the
   whole source, the separator root has positive width.

This packages the genuine SOURCE piece and RIGHT map needed at
the start of a right-to-left canonical flip. Existence of the
required boundary partner and piecewise root coverage are NOT
inferred from the printed regularity/image-closure hypotheses.
Nor is a completed forbidden-source flip asserted here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F W U : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L W} {Source : Structure L U}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- A verified boundary partner of one right-exclusive component
in a finite forbidden-source weak EHN map produces an actual
minimal function-closed rooted piece and a weak EHN realization
of the ENTIRE piece in the full RIGHT target side.

The root set is exactly T, not just contained in T, and the
selected component is literally the original one outside S.
No root-image injection is necessary for the factorization. -/
theorem weakRightComponent_boundaryPartner_hasGenuineFactor
    [Finite U]
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W)
    (hf : Source.IsEHNHomomorphismEmbedding Whole f)
    (x : {z : U // z ∉
      weakFreeRootPart (sL := sL) (iL := iL) f})
    (hxRight : x.1 ∈
      weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f)
    (T : Set U)
    (hT : T = Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph
          (weakFreeRootPart (sL := sL) (iL := iL) f) x)))
    (hTS : T ⊆
      weakFreeRootPart (sL := sL) (iL := iL) f)
    (y : {z : U // z ∉ T})
    (hSep : ¬ ReachOutside Source.graph T
      (outsideCutMap hTS x) y)
    (hBoundary : Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph T y)) = T) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData Source n),
      Set.range d.roots = T ∧
      Set.range d.roots ⊆
        weakFreeRootPart (sL := sL) (iL := iL) f ∧
      d.left.1 = x.1 ∧ d.right.1 = y.1 ∧
      componentFrom Source.graph (Set.range d.roots) d.left =
        componentFrom Source.graph
          (weakFreeRootPart (sL := sL) (iL := iL) f) x ∧
      ∃ pRight : geometricPieceVertices Source d → F,
        (geometricFunctionalPiece Source d).IsEHNHomomorphismEmbedding
          Right pRight ∧
        ∀ z, iR (pRight z) = f z.1 := by
  let S : Set U :=
    weakFreeRootPart (sL := sL) (iL := iL) f
  have hSClosed : Source.IsClosed S :=
    weakFreeRootPart_isClosed
      (sL := sL) (iL := iL) f hf.1
  obtain ⟨n, d, hRoot, hRootS, hLeft, hRight, hComp⟩ :=
    finite_componentBoundary_hasGeometricPiece_of_partner
      Source S T hSClosed x hT hTS y hSep hBoundary
  obtain ⟨pRight, hpRight, hMap⟩ :=
    weakGeometricPiece_factor_right_of_exactSharedRootComponent
      hfree f hf d hRootS x hxRight hComp
  exact ⟨n, d, hRoot, hRootS, hLeft, hRight,
    hComp, pRight, hpRight, hMap⟩

/-- Under piecewise FULL irreducible-test coverage of genuine
source roots, and an actual empty-cut path between the two
selected vertices, the same boundary-partner construction
also guarantees POSITIVE root width and INJECTIVE target images
of the ordered root. Thus the result has the precise geometric,
root and one-sided-EHN data needed to invoke a common-full-lift
canonical flip once its other diagram premises are supplied. -/
theorem weakRightComponent_boundaryPartner_hasPositiveInjectiveFactor
    [Finite U]
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W)
    (hf : Source.IsEHNHomomorphismEmbedding Whole f)
    (x : {z : U // z ∉
      weakFreeRootPart (sL := sL) (iL := iL) f})
    (hxRight : x.1 ∈
      weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f)
    (T : Set U)
    (hT : T = Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph
          (weakFreeRootPart (sL := sL) (iL := iL) f) x)))
    (hTS : T ⊆
      weakFreeRootPart (sL := sL) (iL := iL) f)
    (y : {z : U // z ∉ T})
    (hSep : ¬ ReachOutside Source.graph T
      (outsideCutMap hTS x) y)
    (hBoundary : Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph T y)) = T)
    (hCover : GeometricPieceRootsPairwiseCoveredOn Source
      (weakFreeRootPart (sL := sL) (iL := iL) f))
    (hConnected : ReachOutside Source.graph (∅ : Set U)
      (⟨x.1, by simp⟩ : {z : U // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : U // z ∉ ∅})) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData Source n),
      0 < n ∧
      Set.range d.roots = T ∧
      Set.range d.roots ⊆
        weakFreeRootPart (sL := sL) (iL := iL) f ∧
      Function.Injective (fun i : Fin n => f (d.roots i)) ∧
      ∃ pRight : geometricPieceVertices Source d → F,
        (geometricFunctionalPiece Source d).IsEHNHomomorphismEmbedding
          Right pRight ∧
        ∀ z, iR (pRight z) = f z.1 := by
  let S : Set U :=
    weakFreeRootPart (sL := sL) (iL := iL) f
  obtain ⟨n, d, hRoot, hRootS, hLeft, hRight,
      _hComp, pRight, hpRight, hMap⟩ :=
    weakRightComponent_boundaryPartner_hasGenuineFactor
      hfree f hf x hxRight T hT hTS y hSep hBoundary
  have hPathD : ReachOutside Source.graph (∅ : Set U)
      (⟨d.left.1, by simp⟩ : {z : U // z ∉ ∅})
      (⟨d.right.1, by simp⟩ : {z : U // z ∉ ∅}) := by
    simpa only [hLeft, hRight] using hConnected
  have hn : 0 < n :=
    geometricPiece_positiveWidth_of_emptyCut_path Source d hPathD
  have hInj : Function.Injective (fun i : Fin n => f (d.roots i)) :=
    geometricRootImage_injective_of_piecewiseCover
      Source S Whole f hf hCover d hRootS
  exact ⟨n, d, hn, hRoot, hRootS,
    hInj, pRight, hpRight, hMap⟩

/-- When the full generated boundary T contains at most ONE vertex,
the same actual right-side component construction has an
automatically injective ordered TARGET root tuple. No EHN test-cover
assumption is needed: the roots are distinct SOURCE vertices all
lying in a singleton, so the root index itself has at most one
element. Positivity still uses an actual path in the full source.

This is a useful direct one-root case of the original 2019
distinct-root canonical lift. It does not assert the complementary
full-lift diagram or existence of a boundary partner. -/
theorem weakRightComponent_singletonBoundary_hasPositiveInjectiveFactor
    [Finite U]
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W)
    (hf : Source.IsEHNHomomorphismEmbedding Whole f)
    (x : {z : U // z ∉
      weakFreeRootPart (sL := sL) (iL := iL) f})
    (hxRight : x.1 ∈
      weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f)
    (T : Set U)
    (hT : T = Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph
          (weakFreeRootPart (sL := sL) (iL := iL) f) x)))
    (hTS : T ⊆
      weakFreeRootPart (sL := sL) (iL := iL) f)
    (hSingleton : ∀ a b : U, a ∈ T → b ∈ T → a = b)
    (y : {z : U // z ∉ T})
    (hSep : ¬ ReachOutside Source.graph T
      (outsideCutMap hTS x) y)
    (hBoundary : Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph T y)) = T)
    (hConnected : ReachOutside Source.graph (∅ : Set U)
      (⟨x.1, by simp⟩ : {z : U // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : U // z ∉ ∅})) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData Source n),
      0 < n ∧
      Set.range d.roots = T ∧
      Function.Injective (fun i : Fin n => f (d.roots i)) ∧
      ∃ pRight : geometricPieceVertices Source d → F,
        (geometricFunctionalPiece Source d).IsEHNHomomorphismEmbedding
          Right pRight ∧
        ∀ z, iR (pRight z) = f z.1 := by
  obtain ⟨n, d, hRoot, _hRootS, hLeft, hRight, _hComp,
      pRight, hpRight, hMap⟩ :=
    weakRightComponent_boundaryPartner_hasGenuineFactor
      hfree f hf x hxRight T hT hTS y hSep hBoundary
  have hPathD : ReachOutside Source.graph (∅ : Set U)
      (⟨d.left.1, by simp⟩ : {z : U // z ∉ ∅})
      (⟨d.right.1, by simp⟩ : {z : U // z ∉ ∅}) := by
    simpa only [hLeft, hRight] using hConnected
  have hn : 0 < n :=
    geometricPiece_positiveWidth_of_emptyCut_path Source d hPathD
  have hInj : Function.Injective
      (fun i : Fin n => f (d.roots i)) := by
    intro i j _hEq
    apply d.roots_injective
    apply hSingleton
    · rw [← hRoot]
      exact ⟨i, rfl⟩
    · rw [← hRoot]
      exact ⟨j, rfl⟩
  exact ⟨n, d, hn, hRoot, hInj, pRight, hpRight, hMap⟩


end AllThoseRamseyClasses.Lifts
