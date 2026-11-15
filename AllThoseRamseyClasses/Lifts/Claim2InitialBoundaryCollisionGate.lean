import AllThoseRamseyClasses.Lifts.Claim2LocalBoundaryCollisionTrichotomy
import AllThoseRamseyClasses.Lifts.Claim2OriginalMinimizerObstructionReduction

/-!
# Initial B-active boundary injection or a genuine localized source collision

The original Claim 2 minimizer may have a weak, noninjective EHN
map. We MUST NOT presume that the ordered outer-root target tuple
being injective makes all B-active generated boundaries injective.

In a genuine geometric piece whose root maps into the common
target seam, the no-escape lemma nevertheless ensures that each
complete generated B-component boundary lies inside the old
outer source piece and the full seam preimage. Thus failure of
the initial boundary-injectivity invariant is certified by TWO
distinct literal SOURCE vertices u,v in that one generated
boundary with identical weak target images.

No positive B-rank, source connectedness or forbidden-lift equality
is needed for this initialization dichotomy. In particular this
does NOT repair the collision, quotient the weak target images or
establish an unrestricted Claim 2.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The exact native initial B-boundary-injectivity condition for
one genuine geometric source piece, or a specific generated-boundary
collision inside the old outer piece and target seam.

In the collision branch the generated set T is exactly the full
function closure of the native Gaifman component's neighborhood;
u and v are distinct SOURCE vertices, NOT target-image classes. -/
theorem claim2_initial_activeBoundaryInj_or_localSourceCollision
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    {n : ℕ} (P : GeometricFunctionalPieceData Source n)
    (Target : Structure L UT) (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hOuterRootInSeam : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f) :
    (∀ (x : {v : V //
        v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
      x.1 ∈ geometricPieceVertices Source P →
      x.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f →
      Set.InjOn f
        (Source.functionClosure
          (gaifmanNeighborhood Source.graph
            (componentFrom Source.graph
              (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))) ∨
    (∃ (x : {v : V //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
        (T : Set V),
      x.1 ∈ geometricPieceVertices Source P ∧
      x.1 ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f ∧
      T = Source.functionClosure
        (gaifmanNeighborhood Source.graph
          (componentFrom Source.graph
            (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)) ∧
      T ⊆ weakFreeRootPart (sL := iLeft) (iL := jLeft) f ∩
        geometricPieceVertices Source P ∧
      ∃ v w : V, v ∈ T ∧ w ∈ T ∧ v ≠ w ∧ f v = f w) := by
  classical
  by_cases hActiveBoundaryInjective :
      ∀ (x : {v : V //
          v ∉ weakFreeRootPart (sL := iLeft) (iL := jLeft) f}),
        x.1 ∈ geometricPieceVertices Source P →
        x.1 ∈ weakFreeRightPart
          (sL := iLeft) (iL := jLeft) (iR := jRight) f →
        Set.InjOn f
          (Source.functionClosure
            (gaifmanNeighborhood Source.graph
              (componentFrom Source.graph
                (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))
  · exact Or.inl hActiveBoundaryInjective
  · right
    push_neg at hActiveBoundaryInjective
    obtain ⟨x, hxP, hxRight, hNotInj⟩ := hActiveBoundaryInjective
    let S : Set V :=
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f
    let T : Set V := Source.functionClosure
      (gaifmanNeighborhood Source.graph
        (componentFrom Source.graph S x))
    have hSClosed : Source.IsClosed S :=
      weakFreeRootPart_isClosed
        (sL := iLeft) (iL := jLeft) f hf.1
    have hKClosed :
        Source.IsClosed (geometricPieceVertices Source P) :=
      functionalComponentUnion_isClosed Source
        (Set.range P.roots) P.minimal.1 P.left
    have hNoEscape :
        FunctionalContextNoEscapeOutsideSeam Source S
          (geometricPieceVertices Source P) :=
      geometricPiece_noEscapeOutsideContainingSeam
        Source P S hOuterRootInSeam
    have hTInside : T ⊆ S ∩
        geometricPieceVertices Source P := by
      intro z hz
      exact functionalNoEscape_component_generatedBoundary_inside
        Source S (geometricPieceVertices Source P)
        hSClosed hKClosed hNoEscape x hxP
        (by simpa only [T] using hz)
    have hCollision :
        ∃ v w : V, v ∈ T ∧ w ∈ T ∧ v ≠ w ∧ f v = f w := by
      by_contra hNoCollision
      apply hNotInj
      intro v hv w hw hEq
      by_contra hDistinct
      exact hNoCollision ⟨v, w, hv, hw, hDistinct, hEq⟩
    exact ⟨x, T, hxP, hxRight, rfl, hTInside, hCollision⟩

end AllThoseRamseyClasses.Lifts
