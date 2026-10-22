import AllThoseRamseyClasses.Lifts.WeakSingletonBoundaryPartner
import AllThoseRamseyClasses.Lifts.GlobalSingletonBoundaryRightToLeftFlip

/-!
# Automatic original-global B-to-A flip with a singleton generated boundary

The earlier theorem `globalSingletonBoundary_rightToLeftFlip`
required an explicit boundary partner y, a separation proof and
a matching full generated-boundary equation. In a CONNECTED
weak forbidden source meeting both exclusive sides, that partner
is now constructed from an actual LEFT-exclusive vertex a.

Thus for a right-exclusive source component B whose entire
generated external boundary has at most one vertex, all geometric
flip prerequisites follow from actual source connectivity and the
exact target/free-amalgam data. Root-image injectivity follows
automatically from the one-vertex root. The conclusion is a literal
forbidden-source replacement with an EHN map, including the
unchanged full native complementary structure.

This is not unrestricted Claim 2: higher-width roots and collision
of different root coordinates remain open. The FULL original
global canonical lift, not merely an old shared shadow, is assumed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A connected left-exclusive source vertex supplies the
otherwise-missing partner needed for an actual B-to-A flip
whenever the right S-component has singleton generated boundary.

No explicit partner, separation, matching closure, positive width,
or root-image injection is assumed. The replacement is a genuine
member of the forbidden family with full native EHN map. -/
theorem globalSingletonBoundary_rightToLeftFlip_of_connectedOpposite
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
    (hTS : T ⊆ weakFreeRootPart
      (sL := iLeft) (iL := jLeft) f)
    (hSingleton : ∀ u v : V, u ∈ T → v ∈ T → u = v)
    (a : V)
    (haLeft : a ∈ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (hConnected : ReachOutside Forbidden.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨a, by simp⟩ : {z : V // z ∉ ∅})) :
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
                 (∀ u : Q.Carrier, flip (iQ u) = jLeft (g u)) ∧
                 (∀ v : C.Carrier, flip (iC v) = f v.1)) := by
  letI : Finite V := hFinite
  obtain ⟨y, hYa, hSep, hYBoundary⟩ :=
    weakRightComponent_singletonBoundary_hasPartner
      hFree f hf x hxRight T hT hTS
      hSingleton a haLeft hConnected
  have hPathY : ReachOutside Forbidden.graph (∅ : Set V)
      (⟨x.1, by simp⟩ : {z : V // z ∉ ∅})
      (⟨y.1, by simp⟩ : {z : V // z ∉ ∅}) := by
    simpa only [hYa] using hConnected
  exact globalSingletonBoundary_rightToLeftFlip
    F Forbidden hFinite hForbidden
    Target f hf Left Right jLeft jRight
    X iLeft iRight hFree hCommon
    x hxRight T hT hTS hSingleton
    y hSep hYBoundary hPathY

end AllThoseRamseyClasses.Lifts
