import AllThoseRamseyClasses.Lifts.Claim2PartnerActualContextualFlip
import AllThoseRamseyClasses.Lifts.WeakSingletonBoundaryPartner

/-!
# Track C: actual local B→A successor when the right boundary is a singleton

The matched boundary-partner and target-root-injectivity hypotheses
of the general conditional contextual flip are *automatic* for a
connected native forbidden source with a nonempty singleton
generated right-component boundary T.

A genuine right-exclusive component B after deleting the complete
source preimage S of the shared target root has generated boundary
T=Cl(N(B)) ⊆ S. Suppose the original outer geometric piece P
contains B and an A-exclusive vertex a in its selected component.
When |T|≤1, the pre-existing singleton boundary theorem produces
an ACTUAL left-component boundary partner inside the SAME source
without any source-support minimality. On a singleton T, any map
f is injective on T, even if f has collisions everywhere else.

The general partner-based source theorem then constructs a true
PROPER B-only geometric inner subpiece. The original global
canonical lift produces a literal forbidden source replacement
with exact outer rooted all-test congruence and STRICTLY LOWER
B-exclusive SOURCE count inside the transported outer context.

This removes partner and root-image injectivity requirements for
the singleton-boundary case, but the NEW outer context still
needs its native minimal-closed-separator recognition before
it can be used as an iterable successor. Nor is the singleton
boundary assumption proved for arbitrary positive local B-rank.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A one-vertex boundary of a right-exclusive S-component
inside a mixed outer geometric source piece guarantees a genuine
proper inner B-only piece and a same-witness original-global
canonical flip with complete all-test profile and strict local
B-source-support decrease.

The source map need not be left-support-minimal OR globally
injective. No externally given boundary partner or InjOn
hypothesis is required. Connectivity of the specified
right/left vertices in the TRUE source is explicit. -/
theorem claim2_actualContextualRightFlip_of_singletonBoundary
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    {n : ℕ} (P : GeometricFunctionalPieceData Forbidden n)
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
    (hOuterRootInSeam : Set.range P.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (x : {v : V // v ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) f)
    (hxOuter : x.1 ∈ functionalComponentFrom Forbidden
      (Set.range P.roots) P.left)
    (a : V)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) f)
    (haOuter : a ∈ functionalComponentFrom Forbidden
      (Set.range P.roots) P.left)
    (T : Set V)
    (hT : T = Forbidden.functionClosure
      (gaifmanNeighborhood Forbidden.graph
        (componentFrom Forbidden.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) f) x)))
    (hTnonempty : T.Nonempty)
    (hSingleton : ∀ u v : V, u ∈ T → v ∈ T → u = v)
    (hConnected : ReachOutside Forbidden.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {v : V // v ∉ ∅})
      (⟨a, by simp⟩ : {v : V // v ∉ ∅})) :
    ∃ (m : ℕ) (d : GeometricFunctionalPieceData Forbidden m),
      0 < m ∧
      geometricPieceVertices Forbidden d ⊂
        geometricPieceVertices Forbidden P ∧
      ∃ (hOuterRootOutside : ∀ i : Fin n,
        P.roots i ∉ functionalComponentFrom Forbidden
          (Set.range d.roots) d.left),
      ∃ (V' : Type) (New : Structure L V'), F New ∧
      ∃ (Q : FunctionalRootExtension
          (geometricGlobalFunctionalChart Forbidden d).root)
        (iQ : Structure.Embedding Q.str New)
        (iE : Structure.Embedding
          (geometricGlobalComplementChart Forbidden d).str New),
        Structure.IsFreeAmalgam Q.rootEmbedding
          (geometricGlobalComplementChart Forbidden d).rootEmbedding iQ iE ∧
        ∃ (flip : V' → UT),
          New.IsEHNHomomorphismEmbedding Target flip ∧
          ∃ (hNewK : New.IsClosed
              (iQ '' (Set.univ : Set Q.Carrier) ∪
                iE '' (oldOuterContextInInnerComplement Forbidden P d)))
            (newRoot : Structure.Embedding
              (geometricGlobalFunctionalChart Forbidden P).root
              (New.induce
                (iQ '' (Set.univ : Set Q.Carrier) ∪
                  iE '' (oldOuterContextInInnerComplement Forbidden P d))
                hNewK)),
            (functionalDiagramPieceSetoid
                (geometricGlobalFunctionalChart Forbidden P).root F).r
              (geometricGlobalFunctionalChart Forbidden P).ext
              ({ Carrier := {w : V' //
                    w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪
                      iE '' (oldOuterContextInInnerComplement Forbidden P d))},
                 str := New.induce
                  (iQ '' (Set.univ : Set Q.Carrier) ∪
                    iE '' (oldOuterContextInInnerComplement Forbidden P d))
                  hNewK,
                 rootEmbedding := newRoot } :
                FunctionalRootExtension
                  (geometricGlobalFunctionalChart Forbidden P).root) ∧
            (∀ i : Fin n,
              (newRoot i).1 =
                iE (⟨P.roots i, hOuterRootOutside i⟩ :
                  (geometricGlobalComplementChart Forbidden d).Carrier) ∧
              flip ((newRoot i).1) = f (P.roots i)) ∧
            Nat.card {w : V' //
              w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪
                iE '' (oldOuterContextInInnerComplement Forbidden P d)) ∧
              flip w ∈ fullFreeRightExclusiveTarget iRight jRight} <
            Nat.card {v : V //
              v ∈ geometricPieceVertices Forbidden P ∧
              f v ∈ fullFreeRightExclusiveTarget iRight jRight} := by
  let S : Set V :=
    weakFreeRootPart (sL := iLeft) (iL := jLeft) f
  have hSclosed : Forbidden.IsClosed S :=
    weakFreeRootPart_isClosed (sL := iLeft) (iL := jLeft) f hf.1
  have hTS : T ⊆ S := by
    intro z hz
    exact functionalClosure_neighborhood_subset_cut
      Forbidden S hSclosed x
      (by simpa only [hT] using hz)
  obtain ⟨y, _hyVal, hSep, hYBoundary⟩ :=
    weakRightComponent_singletonBoundary_hasPartner
      hFree f hf x hxRight T hT hTS
      hSingleton a haLeft hConnected
  have hInjT : Set.InjOn f T := by
    intro u hu v hv _huv
    exact hSingleton u v hu hv
  exact claim2_actualContextualRightFlip_of_boundaryPartner
    F hFiniteF Forbidden hFinite hForbidden
    P Target f hf Left Right jLeft jRight
    X iLeft iRight hFree hCommon
    hOuterRootInSeam x hxRight hxOuter
    a haLeft haOuter
    T hT hTS hTnonempty y hSep hYBoundary hInjT

end AllThoseRamseyClasses.Lifts
