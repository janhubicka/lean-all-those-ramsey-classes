import AllThoseRamseyClasses.Lifts.RightBoundaryPartnerPieceFactor
import AllThoseRamseyClasses.Lifts.GlobalRightToLeftPieceFlip

/-!
# Actual B-to-A forbidden-source flip from a one-point generated boundary

One important special case of the original Section 3 Claim 2
requires NO global source-map injection and NO pairwise
irreducible-test covering assumption.

Suppose a right-exclusive source component C of a finite
forbidden EHN witness outside the common full root preimage
S has generated neighborhood closure T=Cl(N(C)) with
at most one vertex. If the exact source boundary-partner
criterion holds at T, the verified construction produces
a GENUINE geometric forbidden-source piece rooted at T
and selected component exactly C. Assuming the two
distinguished source vertices are connected in the whole
source, T has positive width; its ordered target root
image is automatically injective because T is a singleton.

The full RIGHT-side EHN factorization and the common FULL
canonical lift then permit the checked actual RIGHT-to-LEFT
flip, constructing a new literal member of the forbidden
family with unchanged old complement map and new piece
mapped entirely into Left.

The result is a genuine special-case SOURCE flip, not the
unrestricted unflippable-component/minimality argument:
existence of the boundary partner, positive source path
and a common full canonical lift remain assumptions.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A single-vertex generated boundary and an actual boundary
partner give a real original-global B-to-A flip of a genuine
finite connected forbidden-source geometric piece.

No root-image injectivity or test-cover hypothesis is supplied:
injectivity follows from the singleton boundary. The output
includes a literal forbidden replacement, its full functional
free-amalgam source diagram, a map of the new piece into Left,
and EXACT preservation of f on the complementary source. -/
theorem globalSingletonBoundary_rightToLeftFlip
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    (Target : Structure L UT) (f : V → UT)
    (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (x : {z : V // z ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
    (hxRight : x.1 ∈
      weakFreeRightPart (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (T : Set V)
    (hT : T = Forbidden.functionClosure
      (gaifmanNeighborhood Forbidden.graph
        (componentFrom Forbidden.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))
    (hTS : T ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hSingleton : ∀ a b : V, a ∈ T → b ∈ T → a = b)
    (y : {z : V // z ∉ T})
    (hSep : ¬ ReachOutside Forbidden.graph T
      (outsideCutMap hTS x) y)
    (hBoundary : Forbidden.functionClosure
      (gaifmanNeighborhood Forbidden.graph
        (componentFrom Forbidden.graph T y)) = T)
    (hConnected : ReachOutside Forbidden.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : V // z ∉ ∅})) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData Forbidden n),
      0 < n ∧ Set.range d.roots = T ∧
      (let P := geometricGlobalSelectedChart F Forbidden
        hFinite hForbidden d
       let C := geometricGlobalComplementChart Forbidden d
       ∃ Q : FunctionalRootExtension P.1.root,
         (functionalRootPieceSetoid P.1.root F).r P.1.ext Q ∧
         ∃ g : Q.Carrier → UA,
           Q.str.IsEHNHomomorphismEmbedding Left g ∧
           ∃ (V' : Type) (New : Structure L V'),
             F New ∧
             ∃ (iQ : Structure.Embedding Q.str New)
               (iC : Structure.Embedding C.str New),
               Structure.IsFreeAmalgam
                 Q.rootEmbedding C.rootEmbedding iQ iC ∧
               ∃ flip : V' → UT,
                 New.IsEHNHomomorphismEmbedding Target flip ∧
                 (∀ a : Q.Carrier, flip (iQ a) = jLeft (g a)) ∧
                 (∀ b : C.Carrier, flip (iC b) = f b.1)) := by
  letI : Finite V := hFinite
  obtain ⟨n, d, hn, hRoot, hRootInj,
      pRight, _hpRight, hPieceMap⟩ :=
    weakRightComponent_singletonBoundary_hasPositiveInjectiveFactor
      hFree f hf x hxRight T hT hTS hSingleton
      y hSep hBoundary hConnected
  have hRootS : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f := by
    rw [hRoot]
    exact hTS
  have hNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f := by
    intro z hzC hzLeft
    let zP : geometricPieceVertices Forbidden d :=
      ⟨z, Or.inr hzC⟩
    have hRightImage : f z = jRight (pRight zP) :=
      (hPieceMap zP).symm
    exact (weakFreeLeftPart_not_right
      hFree f hzLeft (pRight zP)) hRightImage
  exact ⟨n, d, hn, hRoot,
    geometricGlobalCommonFullLiftFlip_rightToLeft
      F Forbidden hFinite hForbidden d hn
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      hRootS hNoLeft hRootInj⟩

end AllThoseRamseyClasses.Lifts
