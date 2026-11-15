import AllThoseRamseyClasses.Lifts.Claim2PartialCaptureOppositePureFlip

/-!
# Original A-support minimality forces a captured OLD root in the opposite component

Take the 2019 proof's original global minimizer of A-exclusive
SOURCE support among ALL finite forbidden native sources with
EHN weak maps to the same fixed target full free amalgam.
Choose a globally smallest A/B-mixed geometric piece P within
that finite source. For any genuine smaller positive native root
d inside P and the full target seam, whose distinguished endpoints
both lie in P's original selected component and with A-exclusive
d.right and injective ordered d-root target coordinates:

The opposite d.right component MUST contain an OLD P-root
SOURCE vertex. Otherwise the checked noncapturing-opposite
geometry and global mixed nonroot-size minimality make that
genuine opposite piece B-free and properly nested, enabling an
actual original A-to-B source flip that strictly decreases
A-exclusive SOURCE support. Contradiction to the global original
A-support minimality.

This does NOT imply absence of smaller-root capture in general.
It identifies the exact remaining pattern: a genuine old P-root
SOURCE vertex inside the opposite/A-side d-component. For old
root width 1, any simultaneous capture in d.left/B component
would be impossible because the two components are disjoint.
That width-one consequence is recorded as a separate exact
source-geometric disjointness lemma.

All sets count actual SOURCE vertices, not weak target images.
No arbitrary weak-map global injectivity or root-width decrease.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Under an original A-exclusive SOURCE-support globally minimizing
forbidden weak-map witness, plus a global smallest mixed source
piece P and the actual smaller-root certificate, the OPPOSITE
component necessarily captures some old P-root SOURCE vertex.

This is a necessary geometric consequence, NOT a contradiction
or an unrestricted proof of the printed original Claim 2. -/
theorem claim2_globalAMinimal_forces_oldRootInOppositeComponent
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
    (hDrightA : d.right.1 ∈
      weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hAMinimal : ∀ {W : Type}
      (New : Structure L W) (hNew : F New)
      (g : W → UT),
      New.IsEHNHomomorphismEmbedding Target g →
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
      Nat.card {w : W //
        g w ∈ fullFreeLeftExclusiveTarget iLeft jLeft}) :
    ∃ r : V,
      r ∈ Set.range P.data.roots ∧
      r ∈ functionalComponentFrom Source
        (Set.range d.roots) d.right := by
  classical
  by_contra hNoRoot
  have hNoOppositeOldRoot :
      ∀ r : V, r ∈ Set.range P.data.roots →
        r ∉ functionalComponentFrom Source
          (Set.range d.roots) d.right := by
    intro r hrOld hrOpp
    exact hNoRoot ⟨r, hrOld, hrOpp⟩
  obtain ⟨_hProper, W, New, hNew, flip, hFlip, hStrictA⟩ :=
    claim2_minimalMixed_noOppositeOldRoot_actualLeftSupportFlip
      F hFiniteF Source hFinite hForbidden
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      P hMinimal d hm hDRootInsideP hDleftOld hDrightOld
      hNoOppositeOldRoot hDRootSeam hDRootTargetInjective hDrightA
  exact (Nat.not_lt_of_ge
    (hAMinimal New hNew flip hFlip)) hStrictA

/-- A SINGLE old root cannot be captured by BOTH selected components
of the same genuine minimal closed separator. This native source
path fact is independent of target maps and minimization. -/
theorem claim2_singleOldRoot_cannot_be_captured_on_both_sides
    {V : Type} (Source : Structure L V)
    {m : ℕ}
    (d : GeometricFunctionalPieceData Source m)
    (r : V)
    (hB : r ∈ functionalComponentFrom Source
      (Set.range d.roots) d.left)
    (hA : r ∈ functionalComponentFrom Source
      (Set.range d.roots) d.right) : False := by
  exact (Set.disjoint_left.mp
    (geometricPiece_components_disjoint Source d)) hB hA

end AllThoseRamseyClasses.Lifts
