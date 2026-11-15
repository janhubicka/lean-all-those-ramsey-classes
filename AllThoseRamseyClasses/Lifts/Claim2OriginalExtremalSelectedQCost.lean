import AllThoseRamseyClasses.Lifts.Claim2RefinedEligibleInnerSelection
import AllThoseRamseyClasses.Lifts.Claim2AFreeSelectedQChainMonotonicity
import AllThoseRamseyClasses.Lifts.Claim2OriginalLexMinPrivateQObstruction

/-!
# Track B/C: original all-width extremality eliminates REFINED
          smaller-root obstructions before selecting SAME Q

The verified Track C all-width extremal theorem rules out a
smaller-root component capturing an old outer root OR mixing
A-exclusive and B-exclusive SOURCE vertices when:
* the source/map is an ORIGINAL globally A-exclusive SOURCE
  support-minimizing finite forbidden EHN witness;
* the chosen real seam-rooted outer geometric piece is globally
  MINIMAL among mixed source-geometric pieces by nonroot SOURCE
  vertex count; and
* the selected smaller geometric root has injected TARGET root
  coordinates, B-only distinguished d.left, A-only d.right,
  both endpoints in the ORIGINAL outer selected component.

The older Track B obstruction predicates projected out precisely
those last endpoint certificates. We use the new REFINED native
positive-rank selector to retain them and apply Track C's existing
kernel-checked all-width theorem to remove the smaller-root branch.
This recovers a genuine eligible inner B-only separator at the
ORIGINAL extremal state, then applies the SAME selected-Q A-free
native source replacement (with literal Q+E diagram retained).

At an ORIGINAL globally (A,B)-lex-minimal witness, the resulting
Q has STRICTLY POSITIVE PRIVATE Q-nonroot A-exclusive SOURCE cost.
This makes the obstacle to iterating original extremality precise:
the first selected B→A flip generally leaves the global A-minimum
class, despite being a genuine full-native source replacement.

The theorem does NOT assume extremality persists at later states,
or eliminate initial source-test collisions or prove general
2019 Claim 2/strong amalgamation. Frozen manuscript unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- At an ORIGINAL globally A-source-minimal forbidden native weak
map and an ORIGINAL smallest source-geometric mixed outer piece,
positive B-only SOURCE rank has a GENUINE eligible one-sided
inner separator. The refined smaller-root obstruction would
contradict the checked Track C all-width extremal theorem.

The old outer component equality is explicit: the state s is
built from the SAME selected mixed piece P, not merely another
geometric piece in its source. -/
theorem claim2Native_originalExtremal_positiveRank_hasEligibleInner
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    {n : ℕ} (hn : 0 < n)
    (s : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (P : MixedGeometricPiece s.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) s.f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) s.f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) s.f))
    (hOuterEq : s.outer = P.data)
    (hSmallestMixed : ∀ Q : MixedGeometricPiece s.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) s.f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) s.f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) s.f),
      P.nonrootCount ≤ Q.nonrootCount)
    (hPositive : 0 < claim2NativeBSourceRank s)
    (hGlobalAMin :
      ∀ {W : Type}
        (New : Structure L W) (hNew : F New) (g : W → UT),
        New.IsEHNHomomorphismEmbedding Target g →
        Nat.card {v : s.Carrier //
          s.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
        Nat.card {w : W //
          g w ∈ fullFreeLeftExclusiveTarget iLeft jLeft}) :
    claim2NativeEligibleInner s := by
  rcases claim2Native_positiveRank_eligibleInner_or_refinedSmallerRoot
      F hConnected Target Left Right jLeft jRight
      X iLeft iRight hFree s hPositive with
    hEligible | hRefined
  · exact hEligible
  · obtain ⟨m, d, hm, hDrootInOuter, hdLeftInOuter,
      hdRightInOuter, hDrootSeam, hDrootInjective,
      hdLeftB, hdRightA, hObstruction⟩ := hRefined
    have hDrootInP :
        Set.range d.roots ⊆
          geometricPieceVertices s.source P.data := by
      simpa only [hOuterEq] using hDrootInOuter
    have hdLeftInP :
        d.left.1 ∈ functionalComponentFrom s.source
          (Set.range P.data.roots) P.data.left := by
      simpa only [hOuterEq] using hdLeftInOuter
    have hdRightInP :
        d.right.1 ∈ functionalComponentFrom s.source
          (Set.range P.data.roots) P.data.left := by
      simpa only [hOuterEq] using hdRightInOuter
    have hBadP :
        (∃ r : s.Carrier, r ∈ Set.range P.data.roots ∧
          r ∈ functionalComponentFrom s.source
            (Set.range d.roots) d.left) ∨
        (∃ z : s.Carrier,
          z ∈ functionalComponentFrom s.source
            (Set.range d.roots) d.left ∧
          z ∈ weakFreeLeftPart
            (sL := iLeft) (iL := jLeft) s.f) := by
      rcases hObstruction with hCapture | hMixed
      · exact Or.inl (by simpa only [hOuterEq] using hCapture)
      · exact Or.inr hMixed
    exact False.elim
      (claim2_originalAMinimal_allWidths_no_smallerRootObstruction
        F hFiniteF s.source s.finite s.forbidden
        Target s.f s.hom Left Right jLeft jRight
        X iLeft iRight hFree hCommon
        P hSmallestMixed d hm
        hDrootInP hdLeftInP hdRightInP
        hDrootSeam hDrootInjective hdLeftB hdRightA
        hGlobalAMin hBadP)

/-- At the SAME original extremal finite forbidden native SOURCE
witness, a positive B-exclusive piece has one ACTUAL selected
forbidden Q+old-E full free-amalgam B→A source flip with the
old A-free component and entire Q-provenance stored on its
new full-invariant heterogeneous geometric state transition.
The two smaller-root obstructions are excluded using ORIGINAL
global extremality, not assumed absent at intermediate states. -/
theorem claim2Native_originalExtremal_positiveRank_hasAFreeSelectedQStep
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    {n : ℕ} (hn : 0 < n)
    (s : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (P : MixedGeometricPiece s.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) s.f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) s.f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) s.f))
    (hOuterEq : s.outer = P.data)
    (hSmallestMixed : ∀ Q : MixedGeometricPiece s.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) s.f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) s.f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) s.f),
      P.nonrootCount ≤ Q.nonrootCount)
    (hPositive : 0 < claim2NativeBSourceRank s)
    (hGlobalAMin :
      ∀ {W : Type}
        (New : Structure L W) (hNew : F New) (g : W → UT),
        New.IsEHNHomomorphismEmbedding Target g →
        Nat.card {v : s.Carrier //
          s.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
        Nat.card {w : W //
          g w ∈ fullFreeLeftExclusiveTarget iLeft jLeft}) :
    ∃ t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n,
      claim2NativeAFreeSelectedQStep F Target Left Right
        jLeft jRight X iLeft iRight hn s t := by
  obtain ⟨m, inner, hm, hInnerInside, hOuterRootOutside,
      hInnerSeam, hInnerNoA, hInnerRootInjective,
      x, hxComponent, hxRight⟩ :=
    claim2Native_originalExtremal_positiveRank_hasEligibleInner
      F hFiniteF hConnected Target Left Right jLeft jRight
      X iLeft iRight hFree hCommon hn s
      P hOuterEq hSmallestMixed hPositive hGlobalAMin
  exact claim2Native_eligibleInner_hasAFreeSelectedQStep
    F hFiniteF Target Left Right jLeft jRight
    X iLeft iRight hFree hCommon hn hm
    s inner hInnerInside hOuterRootOutside
    hInnerSeam hInnerNoA hInnerRootInjective
    x hxComponent hxRight

/-- Sharpen the original-extremal selected-Q source theorem by
also minimizing the ORIGINAL B-exclusive SOURCE count among
global A ties. At positive B-source rank a real one-sided
same-Q source successor exists, but lex-minimality forces it
to insert a STRICTLY POSITIVE number of A-exclusive Q-private
nonroot SOURCE vertices. The selected forbidden Q, its full
old-complement native diagram and A-free removed component
are retained in the SAME new state.

This is a positive structural obstruction to the tempting but
invalid argument that the original extremal selected Q can
always be chosen A-neutral. It does NOT claim A-minimality of
the new witness, or provide an unrestricted Claim 2 proof. -/
theorem claim2Native_originalLexExtremal_positiveRank_selectedQ_paysPrivateA
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    {n : ℕ} (hn : 0 < n)
    (s : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n)
    (P : MixedGeometricPiece s.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) s.f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) s.f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) s.f))
    (hOuterEq : s.outer = P.data)
    (hSmallestMixed : ∀ Q : MixedGeometricPiece s.source
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) s.f)
      (weakFreeLeftPart (sL := iLeft) (iL := jLeft) s.f)
      (weakFreeRightPart (sL := iLeft) (iL := jLeft)
        (iR := jRight) s.f),
      P.nonrootCount ≤ Q.nonrootCount)
    (hPositive : 0 < claim2NativeBSourceRank s)
    (hGlobalAMin :
      ∀ {W : Type}
        (New : Structure L W) (hNew : F New) (g : W → UT),
        New.IsEHNHomomorphismEmbedding Target g →
        Nat.card {v : s.Carrier //
          s.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} ≤
        Nat.card {w : W //
          g w ∈ fullFreeLeftExclusiveTarget iLeft jLeft})
    (hBMinAtA :
      ∀ {Z : Type} (Candidate : Structure L Z)
        (hCandidate : F Candidate) (g : Z → UT),
        Candidate.IsEHNHomomorphismEmbedding Target g →
        Nat.card {z : Z //
          g z ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
        Nat.card {v : s.Carrier //
          s.f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} →
        Nat.card {v : s.Carrier //
          s.f v ∈ fullFreeRightExclusiveTarget iRight jRight} ≤
        Nat.card {z : Z //
          g z ∈ fullFreeRightExclusiveTarget iRight jRight}) :
    ∃ t : Claim2NativeGeometricState F Target Left Right
      jLeft jRight X iLeft iRight n,
      claim2NativeAFreeSelectedQStep F Target Left Right
        jLeft jRight X iLeft iRight hn s t ∧
      ∃ (m : ℕ) (inner : GeometricFunctionalPieceData s.source m)
        (Q : FunctionalRootExtension
          (geometricGlobalFunctionalChart s.source inner).root)
        (iQ : Structure.Embedding Q.str t.source),
        0 < Nat.card {q : Q.Carrier //
          q ∉ Set.range Q.rootEmbedding ∧
          t.f (iQ q) ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
  obtain ⟨t, hStep⟩ :=
    claim2Native_originalExtremal_positiveRank_hasAFreeSelectedQStep
      F hFiniteF hConnected Target Left Right jLeft jRight
      X iLeft iRight hFree hCommon hn s
      P hOuterEq hSmallestMixed hPositive hGlobalAMin
  obtain ⟨m, inner, Q, iQ, hPrivatePositive⟩ :=
    claim2NativeOriginalLexMin_AFreeSelectedQStep_positivePrivateACost
      F Target Left Right jLeft jRight X iLeft iRight
      hn s t hStep hGlobalAMin hBMinAtA
  exact ⟨t, hStep, m, inner, Q, iQ, hPrivatePositive⟩

end AllThoseRamseyClasses.Lifts
