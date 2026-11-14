import AllThoseRamseyClasses.Lifts.Claim2WidthOneOriginalMinimizerNoCapture
import AllThoseRamseyClasses.Lifts.Claim2MinimalMixedSmallerRootCapture

/-!
# The entire smaller-root obstruction is excluded at old width one
# under the actual original extremal source-witness hypotheses

The local positive B-source-rank Claim 2 theorem gives either
a REAL rank-decreasing B-to-A flip or a genuine smaller positive
minimal closed separator d. Its smaller-root source certificate
can fail an immediate B-to-A flip if d's selected component:
  (a) captures an old P-root vertex; or
  (b) is A/B-mixed.

In a finite forbidden ORIGINAL source whose weak map globally
MINIMIZES A-exclusive SOURCE support, let P also be globally
minimum NONROOT-size among genuine A/B-mixed source pieces
rooted in the complete target seam. If the old P root has width
one, the two smaller-root alternatives BOTH imply impossible
old-root B-side capture:
  (a) does so directly;
  (b) by the verified source minimal-mixed-piece capture theorem.

But global original A-support minimality and the actual opposite
source piece argument force an old root into d's opposite/A-side
component. As the old root has only one genuine SOURCE vertex,
that vertex cannot simultaneously belong to d's distinct
B and A components. Contradiction.

This is the precise SMALLER-ROOT obstruction exit at width one.
It does not assert an initial positive state exists, preservation
of global A-minimality along B-to-A flips, or terminal zero-B-rank
A-clearing. Higher width split capture remains open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under the actual ORIGINAL A-source minimization and global
smallest mixed SOURCE piece conditions, and at P.root width ONE,
a selected positive smaller root inside the full seam cannot
have EITHER an old P-root captured by its B-side component
OR an A-exclusive SOURCE vertex inside that B-side component.

The smaller root has injective ordered target coordinates as
in the merged positive-rank active-boundary dichotomy.
This is a conditional obstruction-exclusion theorem, not
the full global Claim 2 descent. -/
theorem claim2_originalAMinimal_widthOne_no_smallerRootObstruction
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
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
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (P : MixedGeometricPiece Source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) f))
    (hMinimal : ∀ Q : MixedGeometricPiece Source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) f),
      P.nonrootCount ≤ Q.nonrootCount)
    (hWidthOne : P.width = 1)
    {m : ℕ} (d : GeometricFunctionalPieceData Source m)
    (hm : 0 < m)
    (hDRootInsideP :
      Set.range d.roots ⊆ geometricPieceVertices Source P.data)
    (hDleftOld :
      d.left.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hDrightOld :
      d.right.1 ∈ functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hDRootSeam : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hDRootTargetInjective :
      Function.Injective (fun i : Fin m => f (d.roots i)))
    (hDleftB : d.left.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (hDrightA : d.right.1 ∈
      weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hAMinimal : ∀ {W : Type}
      (New : Structure L W) (hNew : F New)
      (g : W → UT),
      New.IsEHNHomomorphismEmbedding Target g →
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
      Nat.card {w : W //
        g w ∈ fullFreeLeftExclusiveTarget iLeft jLeft})
    (hObstruction :
      (∃ r : V, r ∈ Set.range P.data.roots ∧
        r ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left) ∨
      (∃ a : V,
        a ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left ∧
        a ∈ weakFreeLeftPart
          (sL := iLeft) (iL := jLeft) f)) : False := by
  letI : Finite V := hFinite
  have hCapture :
      ∃ r : V, r ∈ Set.range P.data.roots ∧
        r ∈ functionalComponentFrom Source
          (Set.range d.roots) d.left := by
    rcases hObstruction with hCapture | hMixed
    · exact hCapture
    · exact claim2_minimalMixed_smallerMixed_capturesOldRoot
        Source
        (weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
        (weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
        (weakFreeRightPart (sL := iLeft) (iL := jLeft)
          (iR := jRight) f)
        P hMinimal d hm hDRootSeam
        hDleftOld hDrightOld hMixed
        ⟨d.left.1,
          componentFrom_root Source.graph (Set.range d.roots) d.left,
          hDleftB⟩
  exact claim2_originalAMinimal_widthOne_excludes_selectedCapture
    F hFiniteF Source hFinite hForbidden
    Target f hf Left Right jLeft jRight
    X iLeft iRight hFree hCommon
    P hMinimal d hm hDRootInsideP hDleftOld hDrightOld
    hDRootSeam hDRootTargetInjective hDrightA hAMinimal
    hWidthOne hCapture

end AllThoseRamseyClasses.Lifts
