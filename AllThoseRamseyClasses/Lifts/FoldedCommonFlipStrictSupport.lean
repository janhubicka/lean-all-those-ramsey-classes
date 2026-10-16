import AllThoseRamseyClasses.Lifts.FoldedCommonGlobalDiagramFlip
import AllThoseRamseyClasses.Lifts.CommonLiftFlipStrictSupport
import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram

/-!
# Conditional strict support decrease via a common FOLDED global lift

Unlike the printed distinct-root lift, the auxiliary folded canonical
lift records root-pattern realizations with colliding image
coordinates. Under a genuine common FULL folded lift X, the already
verified actual forbidden-source diagram flip therefore works
without assuming root-image injectivity.

If a selected component contains a source vertex mapping to
Left minus the common root X, the replacement piece maps into
Right, the complementary source map is unchanged, and the number
of source vertices mapping Left-only STRICTLY decreases.

The output is an actual forbidden structure with a weak EHN map.
This removes the root-image injectivity condition from the
CONDITIONAL first minimality contradiction, but at the price of
assuming common folded canonical lifts, a different expansion
whose precompactness and class strong amalgamation remain open.
The printed 2019 strong-amalgamation theorem is NOT certified.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- The whole conditional Claim 1 support inequality in the
auxiliary FOLDED global lift. The original weak forbidden map may
have any collisions, including on the entire ordered root tuple;
no injectivity of source-to-target map is assumed. -/
theorem geometricFoldedCommonFullLiftFlip_strict_leftSupport
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    (d : GeometricFunctionalPieceData Forbidden n) (hn : 0 < n)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonFoldedGlobalCanonicalLift
      F X Left Right iLeft iRight)
    (pLeft : (geometricGlobalFunctionalChart Forbidden d).ext.Carrier → UA)
    (hpLeft : Structure.IsEHNHomomorphismEmbedding
      (geometricGlobalFunctionalChart Forbidden d).ext.str
      Left pLeft)
    (hPieceMap : ∀ z :
      (geometricGlobalFunctionalChart Forbidden d).ext.Carrier,
      jLeft (pLeft z) = f z.1)
    (xsX : Fin n → UX)
    (hRootLeft : ∀ i : Fin n,
      pLeft ((geometricGlobalFunctionalChart Forbidden d).ext.rootEmbedding i)
        = iLeft (xsX i))
    (oldVertex : V)
    (hvComponent : oldVertex ∈
      functionalComponentFrom Forbidden (Set.range d.roots) d.left)
    (hvLeft : oldVertex ∈
      weakFreeLeftPart (sL := iLeft) (iL := jLeft) f) :
    ∃ (W : Type) (New : Structure L W),
      F New ∧
      ∃ flip : W → UT,
        New.IsEHNHomomorphismEmbedding Target flip ∧
        Nat.card {w : W //
          flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} <
        Nat.card {v : V //
          f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
  classical
  let P : SelectedFunctionalChart F n :=
    geometricGlobalSelectedChart F Forbidden hFinite hForbidden d
  let T := geometricGlobalComplementChart Forbidden d
  let pT : T.Carrier → UT := fun b => f b.1
  have hpT : T.str.IsEHNHomomorphismEmbedding Target pT :=
    hf.comp
      (functionalComponentComplementEmbedding Forbidden
        (Set.range d.roots) d.minimal.1 d.left).isEHNHomomorphismEmbedding
  have hOld : forbiddenFunctionalDiagram P.1.root F P.1.ext T :=
    geometricGlobalSource_has_forbidden_diagram
      F Forbidden hFinite hForbidden d
  have hTargetAgree (r : UX) :
      jLeft (iLeft r) = jRight (iRight r) :=
    (hTargetFree.overlap (iLeft r) (iRight r)).mpr
      ⟨r, rfl, rfl⟩
  have hRootTarget : ∀ i : Fin n,
      jLeft (pLeft (P.1.ext.rootEmbedding i)) =
        pT (T.rootEmbedding i) := by
    intro i
    calc
      jLeft (pLeft (P.1.ext.rootEmbedding i)) =
          f (d.roots i) := hPieceMap _
      _ = pT (T.rootEmbedding i) := by rfl
  obtain ⟨Q, _hEq, g, _hg, _hRoot,
      W, New, hNewForbidden, iQ, iT,
      hNewFree, flip, hFlip, hFlipQ, hFlipT⟩ :=
    selectedFoldedCommonFullLiftDiagramFlip
      F P hn T hOld X Left Right Target
      iLeft iRight jLeft jRight hCommon hTargetAgree
      pLeft hpLeft pT hpT xsX hRootLeft hRootTarget
  let iOldT :=
    functionalComponentComplementEmbedding Forbidden
      (Set.range d.roots) d.minimal.1 d.left
  letI : Fintype V := Fintype.ofFinite V
  letI : Finite W := hFiniteF New hNewForbidden
  letI : Fintype W := Fintype.ofFinite W
  letI : Finite T.Carrier :=
    Finite.of_injective (fun b : T.Carrier => b.1) (by
      intro a b hab
      exact Subtype.ext hab)
  letI : Fintype T.Carrier := Fintype.ofFinite T.Carrier
  have hOldRight : ∀ b : T.Carrier,
      f (iOldT b) = f b.1 := by
    intro b
    rfl
  have hOutside : ∀ b : T.Carrier,
      oldVertex ≠ iOldT b := by
    intro b hb
    have hv : oldVertex = b.1 := hb
    have hbComponent : b.1 ∈
        functionalComponentFrom Forbidden (Set.range d.roots)
          d.left := hv ▸ hvComponent
    exact b.2 hbComponent
  have hNewLeftAvoid : ∀ a : Q.Carrier,
      flip (iQ a) ∉ fullFreeLeftExclusiveTarget iLeft jLeft := by
    intro a
    rw [hFlipQ a]
    exact freeRight_avoids_fullLeftExclusiveTarget
      iLeft iRight jLeft jRight hTargetFree (g a)
  have hOldLeftTarget :
      f oldVertex ∈ fullFreeLeftExclusiveTarget iLeft jLeft :=
    (weakFreeLeftPart_iff_targetExclusive
      iLeft jLeft f oldVertex).mp hvLeft
  have hStrict :
      Nat.card {w : W //
        flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} <
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
    exact flipExclusiveSupport_strict_decrease
      (iOldR := iOldT)
      (iNewL := iQ)
      (iNewR := iT)
      (sNewL := Q.rootEmbedding)
      (sRight := T.rootEmbedding)
      hNewFree f flip (fun b : T.Carrier => f b.1)
      hOldRight hFlipT
      (fullFreeLeftExclusiveTarget iLeft jLeft)
      hNewLeftAvoid oldVertex hOldLeftTarget hOutside
  exact ⟨W, New, hNewForbidden, flip, hFlip, hStrict⟩

end AllThoseRamseyClasses.Lifts
