import AllThoseRamseyClasses.Lifts.Claim2AMinimalOppositeRootCapture

/-!
# Width-one selected-root capture is impossible under original A-minimality

The prior checked local positive-rank geometry yields a true
selected B-side smaller separator d, but d's selected component
may capture old separator-root vertices. Global minimum A-support
of the ORIGINAL forbidden source/weak map, together with global
smallest nonroot-size A/B-mixed piece P and injectivity of d's
ordered TARGET root, forces an OLD P-root into the OPPOSITE
A-side d-component.

When the entire old P-root has only one SOURCE vertex, it cannot
also lie in d's selected B component: the two genuine minimal-cut
components are disjoint. Thus the width-one captured-B-side
alternative is excluded under the explicitly stated extremal
hypotheses.

This is NOT a proof of the full original Claim 2. It does not
handle higher root width split capture, prove the zero-B-rank
terminal step, or justify arbitrary initial root-image injection.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A complete geometric root whose ordered source index has
width ONE has only one actual SOURCE vertex. No target map. -/
theorem claim2_geometricRoot_unique_of_widthOne
    {V : Type} (Source : Structure L V)
    {n : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (hn : n = 1) :
    ∀ r s : V,
      r ∈ Set.range P.roots →
      s ∈ Set.range P.roots →
      r = s := by
  intro r s hr hs
  obtain ⟨i, hi⟩ := hr
  obtain ⟨j, hj⟩ := hs
  have hSub : Subsingleton (Fin n) := by
    rw [hn]
    infer_instance
  have hij : i = j := @Subsingleton.elim (Fin n) hSub i j
  calc
    r = P.roots i := hi.symm
    _ = P.roots j := congrArg P.roots hij
    _ = s := hj

/-- Original global A-source-support minimality plus minimal mixed
P forces a captured old root on the opposite d.side. Hence the
selected B-side cannot simultaneously capture its unique old
root vertex. No root width is assumed here, only uniqueness
of its actual set of SOURCE vertices. -/
theorem claim2_originalAMinimal_uniqueOldRoot_excludes_selectedCapture
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
    (∀ r s : V,
      r ∈ Set.range P.data.roots →
      s ∈ Set.range P.data.roots → r = s) →
    (∃ r : V,
      r ∈ Set.range P.data.roots ∧
      r ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left) → False := by
  intro hUnique hSelectedCapture
  obtain ⟨rOpp, hrOppRoot, hrOppComponent⟩ :=
    claim2_globalAMinimal_forces_oldRootInOppositeComponent
      F hFiniteF Source hFinite hForbidden
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      P hMinimal d hm hDRootInsideP hDleftOld hDrightOld
      hDRootSeam hDRootTargetInjective hDrightA hAMinimal
  obtain ⟨rB, hrBRoot, hrBComponent⟩ := hSelectedCapture
  have hEq : rB = rOpp := hUnique rB rOpp hrBRoot hrOppRoot
  have hrOppAtB : rB ∈ functionalComponentFrom Source
      (Set.range d.roots) d.right := by
    simpa only [hEq] using hrOppComponent
  exact claim2_singleOldRoot_cannot_be_captured_on_both_sides
    Source d rB hrBComponent hrOppAtB

/-- Specialized old-root-width-one source exclusion, still
conditional on the original extremal witness hypotheses. -/
theorem claim2_originalAMinimal_widthOne_excludes_selectedCapture
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
    P.width = 1 →
    (∃ r : V,
      r ∈ Set.range P.data.roots ∧
      r ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left) → False := by
  intro hWidthOne hSelectedCapture
  have hUnique :
      ∀ r s : V,
        r ∈ Set.range P.data.roots →
        s ∈ Set.range P.data.roots → r = s :=
    claim2_geometricRoot_unique_of_widthOne Source P.data hWidthOne
  exact claim2_originalAMinimal_uniqueOldRoot_excludes_selectedCapture
      F hFiniteF Source hFinite hForbidden
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      P hMinimal d hm hDRootInsideP hDleftOld hDrightOld
      hDRootSeam hDRootTargetInjective hDrightA hAMinimal
    hUnique hSelectedCapture

end AllThoseRamseyClasses.Lifts
