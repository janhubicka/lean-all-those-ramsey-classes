import AllThoseRamseyClasses.Lifts.CommonLiftFlipStrictSupport
import AllThoseRamseyClasses.Lifts.GeometricPieceSideDichotomy
import AllThoseRamseyClasses.Lifts.GeometricCommonRootCoordinates
import AllThoseRamseyClasses.Lifts.GlobalRightToLeftStrictSupport

/-!
# Terminal zero-B-source-rank exit by a genuine Left-to-Right forbidden-source flip

The original 2019 Claim 2 descent aims to eliminate B-exclusive
SOURCE vertices from an A-anchored genuine geometric outer piece.
If the local B-exclusive SOURCE rank is literally zero, then its
entire selected nonroot component contains NO right-exclusive
source vertex, even when the weak EHN source map has collisions.
The actual source geometric piece therefore weakly factors
through the FULL Left target.

If the ordered target-root image is injective, and the selected
component has an A-exclusive SOURCE vertex, the verified global
common-canonical-lift source flip produces a REAL new forbidden
source/weak map with STRICTLY LESS A-exclusive SOURCE support.

Thus zero local B SOURCE rank is inconsistent with ORIGINAL GLOBAL
A-source-support minimality, whenever the selected root images are
injected. At root width one the latter is AUTOMATIC, without any
whole-seam injectivity.

This is an ACTUAL terminal conditional contradiction, not an
induction across positive B-rank states. The positive B->A flip
is not known to preserve original global A-minimality.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Zero B-exclusive SOURCE rank on a finite genuine geometric
piece implies its entire selected nonroot component is B-free.
There is NO assumption that the EHN weak source map is injective. -/
theorem claim2_zeroBSourceRank_selectedComponent_noRight
    {V UX UA UB UT : Type}
    (Source : Structure L V) (hFinite : Finite V)
    {n : ℕ} (P : GeometricFunctionalPieceData Source n)
    (Target : Structure L UT) (f : V → UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hZeroB :
      Nat.card {v : V //
        v ∈ geometricPieceVertices Source P ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} = 0) :
    ∀ z : V,
      z ∈ functionalComponentFrom Source
        (Set.range P.roots) P.left →
      z ∉ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f := by
  classical
  letI : Finite V := hFinite
  letI : Fintype V := Fintype.ofFinite V
  have hTargetAgree :
      ∀ r : UX, jRight (iRight r) = jLeft (iLeft r) := by
    intro r
    exact ((hFree.overlap (iLeft r) (iRight r)).mpr
      ⟨r, rfl, rfl⟩).symm
  intro z hzComponent hzRight
  have hzSwapped :
      z ∈ weakFreeLeftPart
        (sL := iRight) (iL := jRight) f := by
    refine ⟨hzRight.1, ?_⟩
    intro hzRightRoot
    obtain ⟨r, hr⟩ := hzRightRoot
    apply hzRight.2
    exact ⟨r, (hTargetAgree r).symm.trans hr⟩
  have hzB :
      f z ∈ fullFreeRightExclusiveTarget iRight jRight :=
    (weakFreeLeftPart_iff_targetExclusive iRight jRight f z).mp hzSwapped
  have hNonempty :
      Nonempty {v : V //
        v ∈ geometricPieceVertices Source P ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} :=
    ⟨⟨z, Or.inr hzComponent, hzB⟩⟩
  have hPos :
      0 < Nat.card {v : V //
        v ∈ geometricPieceVertices Source P ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr hNonempty
  exact (Nat.ne_of_gt hPos) hZero

/-- At zero local B-SOURCE rank a true native geometric piece
with complete root in the target seam factors through the FULL
Left target as an actual EHN weak piece map. Root tuple
injectivity is NOT needed for this source factorization. -/
theorem claim2_zeroBSourceRank_actualGeometricPiece_factorsLeft
    {V UX UA UB UT : Type}
    (Source : Structure L V) (hFinite : Finite V)
    {n : ℕ} (P : GeometricFunctionalPieceData Source n)
    (Target : Structure L UT) (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hRoots : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hZeroB :
      Nat.card {v : V //
        v ∈ geometricPieceVertices Source P ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} = 0) :
    ∃ pLeft : geometricPieceVertices Source P → UA,
      (geometricFunctionalPiece Source P).IsEHNHomomorphismEmbedding
        Left pLeft ∧
      ∀ z, jLeft (pLeft z) = f z.1 := by
  have hNoRight :=
    claim2_zeroBSourceRank_selectedComponent_noRight
      Source hFinite P Target f Left Right jLeft jRight
      X iLeft iRight hFree hZeroB
  exact weakGeometricPiece_factor_left_if_no_right
    hFree f hf P hRoots hNoRight

/-- On an A-anchored piece with zero B-exclusive SOURCE rank,
a true global FULL canonical lift and an injective ordered
target root produce a REAL new forbidden native source with
STRICTLY LESS total A-exclusive SOURCE support. This is
an original-source statement, not an image-cardinality shortcut. -/
theorem claim2_zeroBSourceRank_Aanchor_actualStrictAFlip
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V) (hForbidden : F Source)
    {n : ℕ} (P : GeometricFunctionalPieceData Source n)
    (hn : 0 < n)
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
    (hRoots : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hZeroB :
      Nat.card {v : V //
        v ∈ geometricPieceVertices Source P ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} = 0)
    (hRootImageInjective :
      Function.Injective (fun i : Fin n => f (P.roots i)))
    (a : V)
    (haComp : a ∈ functionalComponentFrom Source
      (Set.range P.roots) P.left)
    (haA : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f) :
    ∃ (W : Type) (New : Structure L W) (hNew : F New)
      (flip : W → UT),
      New.IsEHNHomomorphismEmbedding Target flip ∧
      Nat.card {w : W //
        flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} <
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
  obtain ⟨pLeft, hpLeft, hPieceMap⟩ :=
    claim2_zeroBSourceRank_actualGeometricPiece_factorsLeft
      Source hFinite P Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hRoots hZeroB
  have hpLeft' :
      Structure.IsEHNHomomorphismEmbedding
        (geometricGlobalFunctionalChart Source P).ext.str
        Left pLeft := hpLeft
  have hPieceMap' :
      ∀ z : (geometricGlobalFunctionalChart Source P).ext.Carrier,
        jLeft (pLeft z) = f z.1 := hPieceMap
  obtain ⟨xsX, hRootLeft⟩ :=
    geometricPiece_commonRootCoordinates
      Source P Target f X Left iLeft jLeft
      pLeft hPieceMap' hRoots
  obtain ⟨W, New, hNew, flip, hFlip, hStrictA⟩ :=
    geometricGlobalCommonFullLiftFlip_strict_leftSupport
      F hFiniteF Source hFinite hForbidden P hn
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      pLeft hpLeft' hPieceMap' xsX hRootLeft
      hRootImageInjective a haComp haA
  exact ⟨W, New, hNew, flip, hFlip, hStrictA⟩

/-- The terminal local B-rank-zero state is IMPOSSIBLE on a
globally original A-exclusive SOURCE-minimizing weak EHN
forbidden witness, if the actual outer ordered target root is
injective. This uses a real source flip to contradict the
literal global minimum, not a claim about image cardinalities. -/
theorem claim2_zeroBSourceRank_contradicts_originalAMinimality
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V) (hForbidden : F Source)
    {n : ℕ} (P : GeometricFunctionalPieceData Source n)
    (hn : 0 < n)
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
    (hRoots : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hZeroB :
      Nat.card {v : V //
        v ∈ geometricPieceVertices Source P ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} = 0)
    (hRootImageInjective :
      Function.Injective (fun i : Fin n => f (P.roots i)))
    (a : V)
    (haComp : a ∈ functionalComponentFrom Source
      (Set.range P.roots) P.left)
    (haA : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (hAMinimal : ∀ {W : Type}
      (New : Structure L W) (hNew : F New)
      (g : W → UT),
      New.IsEHNHomomorphismEmbedding Target g →
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
      Nat.card {w : W //
        g w ∈ fullFreeLeftExclusiveTarget iLeft jLeft}) :
    False := by
  obtain ⟨W, New, hNew, flip, hFlip, hStrictA⟩ :=
    claim2_zeroBSourceRank_Aanchor_actualStrictAFlip
      F hFiniteF Source hFinite hForbidden P hn
      Target f hf Left Right jLeft jRight
      X iLeft iRight hFree hCommon hRoots hZeroB
      hRootImageInjective a haComp haA
  exact (Nat.not_lt_of_ge (hAMinimal New hNew flip hFlip)) hStrictA

/-- At root width ONE the ordered TARGET root is automatically
injective, irrespective of collisions elsewhere in the weak
EHN source map. Thus the original global A-minimizer cannot
contain an A-anchored local ZERO-B-rank geometric piece with
positive width one and full root in the seam. -/
theorem claim2_widthOne_zeroBSourceRank_contradicts_originalAMinimality
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V) (hForbidden : F Source)
    (P : GeometricFunctionalPieceData Source 1)
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
    (hRoots : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hZeroB :
      Nat.card {v : V //
        v ∈ geometricPieceVertices Source P ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} = 0)
    (a : V)
    (haComp : a ∈ functionalComponentFrom Source
      (Set.range P.roots) P.left)
    (haA : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (hAMinimal : ∀ {W : Type}
      (New : Structure L W) (hNew : F New)
      (g : W → UT),
      New.IsEHNHomomorphismEmbedding Target g →
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
      Nat.card {w : W //
        g w ∈ fullFreeLeftExclusiveTarget iLeft jLeft}) :
    False := by
  have hInjective :
      Function.Injective (fun i : Fin 1 => f (P.roots i)) := by
    intro i j _
    exact Subsingleton.elim i j
  exact claim2_zeroBSourceRank_contradicts_originalAMinimality
    F hFiniteF Source hFinite hForbidden P (by decide)
    Target f hf Left Right jLeft jRight
    X iLeft iRight hFree hCommon hRoots hZeroB
    hInjective a haComp haA hAMinimal

end AllThoseRamseyClasses.Lifts
