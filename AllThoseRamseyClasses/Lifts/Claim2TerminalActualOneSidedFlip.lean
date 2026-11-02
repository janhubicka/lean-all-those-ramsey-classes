import AllThoseRamseyClasses.Lifts.Claim2TerminalLeftSupportAccounting
import AllThoseRamseyClasses.Lifts.GeometricPieceSideDichotomy
import AllThoseRamseyClasses.Lifts.GeometricCommonRootCoordinates
import AllThoseRamseyClasses.Lifts.CommonFullGlobalPieceFlip

/-!
# Claim 2: ACTUAL terminal A-to-B piece flip preserving exterior A-support

The original left-support minimality is global, but intermediate
B-to-A source flips may increase left support INSIDE the chosen
outer piece. For the FINAL terminal step, it is enough to clear
the complete selected outer piece into Right and preserve the
left-support count in its unchanged complementary source.

The two lemmas here make the needed source counting concrete.
First, the entire old and new left full-amalgam pieces have
the SAME exterior support counts for any target set, if the
two actual target maps agree on the complete right side.
Second, the original GLOBAL canonical lift constructs a real
forbidden replacement of a genuine B-free outer geometric piece:
its new selected replacement maps entirely into Right, hence
has ZERO left-exclusive vertices. Exact exterior support equality
then allows a contradiction to the ORIGINAL (not intermediate)
minimal forbidden EHN witness, if the original and terminal
outer complements have equal exterior A-support.

The remaining Claim 2 geometry is the existence of a terminal
B-free geometric outer piece with the original rooted all-test
profile and exterior-count invariance. No such conclusion is
hidden in these hypotheses, and the original Section 3 theorem
is not claimed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- In two actual native full free amalgams sharing the SAME
entire right complement, the original target-map support OUTSIDE
the full left piece is unchanged under any replacement on the
left. The proof counts SOURCE vertices, not target images. -/
theorem fullFreeAmalgam_fullLeftOutside_support_card_eq
    {H OL NL E V W T : Type v}
    [Finite V] [Finite W] [Finite E]
    {Root : Structure L H}
    {OldLeft : Structure L OL}
    {NewLeft : Structure L NL}
    {Right : Structure L E}
    {Old : Structure L V}
    {New : Structure L W}
    {sOldL : Structure.Embedding Root OldLeft}
    {sNewL : Structure.Embedding Root NewLeft}
    {sR : Structure.Embedding Root Right}
    {iOldL : Structure.Embedding OldLeft Old}
    {iOldR : Structure.Embedding Right Old}
    {iNewL : Structure.Embedding NewLeft New}
    {iNewR : Structure.Embedding Right New}
    (hOldFree : Structure.IsFreeAmalgam sOldL sR iOldL iOldR)
    (hNewFree : Structure.IsFreeAmalgam sNewL sR iNewL iNewR)
    (f : V → T) (g : W → T) (TargetSet : Set T)
    (hSameE : ∀ e : E, g (iNewR e) = f (iOldR e)) :
    Nat.card {w : W //
      w ∉ iNewL '' (Set.univ : Set NL) ∧ g w ∈ TargetSet} =
    Nat.card {v : V //
      v ∉ iOldL '' (Set.univ : Set OL) ∧ f v ∈ TargetSet} := by
  have hOldRootInLeft :
      iOldR '' (Set.range sR) ⊆
        iOldL '' (Set.univ : Set OL) := by
    rintro z ⟨e, ⟨r, rfl⟩, rfl⟩
    refine ⟨sOldL r, Set.mem_univ _, ?_⟩
    exact (hOldFree.overlap (sOldL r) (sR r)).mpr
      ⟨r, rfl, rfl⟩
  have hNewRootInLeft :
      iNewR '' (Set.range sR) ⊆
        iNewL '' (Set.univ : Set NL) := by
    rintro z ⟨e, ⟨r, rfl⟩, rfl⟩
    refine ⟨sNewL r, Set.mem_univ _, ?_⟩
    exact (hNewFree.overlap (sNewL r) (sR r)).mpr
      ⟨r, rfl, rfl⟩
  have hOldUnion :
      iOldL '' (Set.univ : Set OL) ∪ iOldR '' (Set.range sR) =
        iOldL '' (Set.univ : Set OL) := by
    apply Set.Subset.antisymm
    · intro z hz
      rcases hz with hz | hz
      · exact hz
      · exact hOldRootInLeft hz
    · intro z hz
      exact Or.inl hz
  have hNewUnion :
      iNewL '' (Set.univ : Set NL) ∪ iNewR '' (Set.range sR) =
        iNewL '' (Set.univ : Set NL) := by
    apply Set.Subset.antisymm
    · intro z hz
      rcases hz with hz | hz
      · exact hz
      · exact hNewRootInLeft hz
    · intro z hz
      exact Or.inl hz
  have hOut :=
    fullFreeAmalgam_contextOutside_support_card_eq
      hOldFree hNewFree (Set.range sR)
      (by intro r; exact ⟨r, rfl⟩)
      f g TargetSet hSameE
  rw [hNewUnion, hOldUnion] at hOut
  exact hOut

/-- A literal one-sided A-to-B canonical flip of the ENTIRE
terminal outer geometric piece. Its original forbidden source
may have a noninjective target map away from the selected
positive-width root; only that root's target images are
assumed injective.

The new selected root extension Q maps into Right, so its
full image has no LEFT-exclusive source vertex. On the SAME
new forbidden source and EHN map, the original exterior
A-source cardinality is retained exactly. -/
theorem geometricGlobalTerminalFlip_clearsLeft_and_preservesExterior
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    (hFiniteF : ∀ {Z : Type} (A : Structure L Z), F A → Finite Z)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    {n : ℕ} (d : GeometricFunctionalPieceData Forbidden n)
    (hn : 0 < n)
    (Target : Structure L UT) (f : V → UT)
    (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam
      iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right
      iLeft iRight)
    (hRootInSeam : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hNoRight : ∀ z : V,
      z ∈ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left →
      z ∉ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (hRootInj : Function.Injective
      (fun i : Fin n => f (d.roots i))) :
    ∃ (W : Type) (New : Structure L W), F New ∧
      ∃ (Q : FunctionalRootExtension
        (geometricGlobalFunctionalChart Forbidden d).root)
        (iQ : Structure.Embedding Q.str New)
        (iE : Structure.Embedding
          (geometricGlobalComplementChart Forbidden d).str New),
        Structure.IsFreeAmalgam Q.rootEmbedding
          (geometricGlobalComplementChart Forbidden d).rootEmbedding
          iQ iE ∧
        ∃ flip : W → UT,
          New.IsEHNHomomorphismEmbedding Target flip ∧
          (∀ w : W,
            w ∈ iQ '' (Set.univ : Set Q.Carrier) →
            flip w ∉ fullFreeLeftExclusiveTarget iLeft jLeft) ∧
          Nat.card {w : W //
            w ∉ iQ '' (Set.univ : Set Q.Carrier) ∧
            flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
          Nat.card {v : V //
            v ∉ geometricPieceVertices Forbidden d ∧
            f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
  classical
  obtain ⟨pLeft, hpLeft, hPieceMap⟩ :=
    weakGeometricPiece_factor_left_if_no_right
      hTargetFree f hf d hRootInSeam hNoRight
  have hpLeft' :
      (geometricGlobalFunctionalChart Forbidden d).ext.str
        .IsEHNHomomorphismEmbedding Left pLeft := hpLeft
  have hPieceMap' : ∀ z :
      (geometricGlobalFunctionalChart Forbidden d).ext.Carrier,
      jLeft (pLeft z) = f z.1 := hPieceMap
  obtain ⟨xsX, hRootLeft⟩ :=
    geometricPiece_commonRootCoordinates Forbidden d
      Target f X Left iLeft jLeft pLeft hPieceMap'
      hRootInSeam
  have hTargetAgree (x : UX) :
      jLeft (iLeft x) = jRight (iRight x) :=
    (hTargetFree.overlap (iLeft x) (iRight x)).mpr
      ⟨x, rfl, rfl⟩
  obtain ⟨Q, _hEq, g, _hg, _hRoot,
      W, New, hNewForbidden, iQ, iE, hNewFree,
      flip, hFlip, hQImage, hEImage⟩ :=
    geometricGlobalCommonFullLiftFlip
      F Forbidden hFinite hForbidden d hn
      Target f hf Left Right jLeft jRight
      X iLeft iRight hCommon hTargetAgree
      pLeft hpLeft' hPieceMap' xsX hRootLeft hRootInj
  let E := geometricGlobalComplementChart Forbidden d
  let iOldLeft : Structure.Embedding
      (geometricGlobalFunctionalChart Forbidden d).ext.str
      Forbidden :=
    functionalComponentEmbedding Forbidden
      (Set.range d.roots) d.minimal.1 d.left
  let iOldE : Structure.Embedding E.str Forbidden :=
    functionalComponentComplementEmbedding Forbidden
      (Set.range d.roots) d.minimal.1 d.left
  letI : Finite V := hFinite
  letI : Finite W := hFiniteF New hNewForbidden
  letI : Finite E.Carrier :=
    Finite.of_injective (fun b : E.Carrier => b.1)
      (by intro a b h; exact Subtype.ext h)
  have hOldFree :
      Structure.IsFreeAmalgam
        (geometricGlobalFunctionalChart Forbidden d).ext.rootEmbedding
        E.rootEmbedding iOldLeft iOldE :=
    geometricGlobalSource_freeDiagram Forbidden d
  have hSameE : ∀ b : E.Carrier,
      flip (iE b) = f (iOldE b) := by
    intro b
    exact hEImage b
  have hOldPieceImage :
      iOldLeft '' (Set.univ : Set
        (geometricGlobalFunctionalChart Forbidden d).ext.Carrier) =
      geometricPieceVertices Forbidden d := by
    apply Set.Subset.antisymm
    · rintro v ⟨a, _ha, rfl⟩
      exact a.2
    · intro v hv
      exact ⟨⟨v, hv⟩, Set.mem_univ _, rfl⟩
  have hOutside :
      Nat.card {w : W //
        w ∉ iQ '' (Set.univ : Set Q.Carrier) ∧
        flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
      Nat.card {v : V //
        v ∉ geometricPieceVertices Forbidden d ∧
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
    have hCard :=
      fullFreeAmalgam_fullLeftOutside_support_card_eq
        hOldFree hNewFree f flip
        (fullFreeLeftExclusiveTarget iLeft jLeft) hSameE
    rw [hOldPieceImage] at hCard
    exact hCard
  have hNewNoA :
      ∀ w : W,
        w ∈ iQ '' (Set.univ : Set Q.Carrier) →
        flip w ∉ fullFreeLeftExclusiveTarget iLeft jLeft := by
    intro w hw
    obtain ⟨a, _ha, rfl⟩ := hw
    rw [hQImage a]
    exact freeRight_avoids_fullLeftExclusiveTarget
      iLeft iRight jLeft jRight hTargetFree (g a)
  exact ⟨W, New, hNewForbidden, Q, iQ, iE, hNewFree,
    flip, hFlip, hNewNoA, hOutside⟩

/-- The final B-free outer piece gives a contradiction to the
ORIGINAL globally A-support-minimal forbidden witness, provided
the exterior A-source count in the terminal source still equals
that in the original witness.

The final clearing replacement is CONSTRUCTED from the genuine
global canonical lift. In particular the theorem does not assume
a miraculous final no-A map or assume intermediate sources stay
left-minimal. It still explicitly requires the terminal genuine
geometric piece with injective root coordinates and no B-only
vertex in its selected component. -/
theorem claim2_originalMinimizer_contradicted_by_terminal_BFreePiece
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    (hFiniteF : ∀ {Z : Type} (A : Structure L Z), F A → Finite Z)
    {UT : Type} (Target : Structure L UT)
    {UX UA UB : Type}
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam
      iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right
      iLeft iRight)
    (wOriginal : ForbiddenEHNWitness F Target)
    (hOriginalMin : ∀ t : ForbiddenEHNWitness F Target,
      wOriginal.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
      t.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft))
    (OriginalContext : Set wOriginal.Carrier)
    (hOrigPositiveA : ∃ v : wOriginal.Carrier,
      v ∈ OriginalContext ∧
      wOriginal.toTarget v ∈
        fullFreeLeftExclusiveTarget iLeft jLeft)
    {V : Type} (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    (f : V → UT)
    (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
    {n : ℕ} (d : GeometricFunctionalPieceData Forbidden n)
    (hn : 0 < n)
    (hRootInSeam : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hNoRight : ∀ z : V,
      z ∈ functionalComponentFrom Forbidden
        (Set.range d.roots) d.left →
      z ∉ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (hRootInj : Function.Injective
      (fun i : Fin n => f (d.roots i)))
    (hExteriorOriginal : 
      Nat.card {v : V //
        v ∉ geometricPieceVertices Forbidden d ∧
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
      Nat.card {v : wOriginal.Carrier //
        v ∉ OriginalContext ∧
        wOriginal.toTarget v ∈
          fullFreeLeftExclusiveTarget iLeft jLeft}) : False := by
  obtain ⟨W, New, hNew, Q, iQ, _iE, _hNewFree,
    flip, hFlip, hNoA, hOutside⟩ :=
    geometricGlobalTerminalFlip_clearsLeft_and_preservesExterior
      F hFiniteF Forbidden hFinite hForbidden d hn
      Target f hf Left Right jLeft jRight
      X iLeft iRight hTargetFree hCommon
      hRootInSeam hNoRight hRootInj
  exact minimalForbiddenEHNWitness_no_terminalLeftClearingFlip
    F Target (fullFreeLeftExclusiveTarget iLeft jLeft)
    wOriginal hOriginalMin
    OriginalContext hOrigPositiveA
    New (hFiniteF New hNew) hNew flip hFlip
    (iQ '' (Set.univ : Set Q.Carrier))
    hNoA (hOutside.trans hExteriorOriginal)

end AllThoseRamseyClasses.Lifts
