import AllThoseRamseyClasses.Lifts.Claim2TerminalZeroRightSupport

/-!
# Terminal Claim 2 contradiction for a singleton OUTER geometric root

In the verified general terminal theorem, a zero local B-exclusive
SOURCE count in an actual geometric outer piece yields a final
genuine A-to-B forbidden source flip contradicting the ORIGINAL
minimal A-exclusive SOURCE support, provided:
* the original full outer root lies in the common target seam;
* its target image under the current weak EHN map is INJECTIVE;
* the exterior A-exclusive SOURCE count equals the ORIGINAL count.

For a geometric outer root with exactly one ordered vertex,
target-root-image injectivity is AUTOMATIC for every map:
all functions Fin 1 → Target are injective. Thus an arbitrary
globally noninjective EHN map cannot obstruct the terminal
flip at that root.

This is a genuine restricted endpoint, not a claim that ALL
original outer geometric roots are singletons. The arbitrary
higher-width collision issue and positive-rank successor
construction remain open in the printed Section 3 argument.

No new forbidden image closure, root quotient, hypothesis about
intermediate A-support minimality, or modification of the frozen
2019 manuscript is involved.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A ZERO-B-rank genuine terminal outer geometric source piece
of singleton root width contradicts the ORIGINAL A-minimal
forbidden source, as soon as original/common-root membership
and the exact ORIGINAL exterior A-source count are preserved.

The current weak EHN source→target map is NOT assumed injective,
even on pairs of unrelated source vertices. Target-root-image
injectivity for Fin 1 is proved internally. -/
theorem claim2_originalMinimizer_contradicted_by_zeroTerminalSingletonRoot
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
    (d : GeometricFunctionalPieceData Forbidden 1)
    (hRootInSeam : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hZeroRightCount :
      Nat.card {v : V //
        v ∈ geometricPieceVertices Forbidden d ∧
        f v ∈ fullFreeRightExclusiveTarget iRight jRight} = 0)
    (hExteriorOriginal :
      Nat.card {v : V //
        v ∉ geometricPieceVertices Forbidden d ∧
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} =
      Nat.card {v : wOriginal.Carrier //
        v ∉ OriginalContext ∧
        wOriginal.toTarget v ∈
          fullFreeLeftExclusiveTarget iLeft jLeft}) : False := by
  have hRootImageInjective :
      Function.Injective (fun i : Fin 1 => f (d.roots i)) := by
    intro i j _hEq
    exact Subsingleton.elim i j
  exact claim2_originalMinimizer_contradicted_by_zeroTerminalBSupport
    F hFiniteF Target Left Right jLeft jRight
    X iLeft iRight hTargetFree hCommon
    wOriginal hOriginalMin OriginalContext hOrigPositiveA
    Forbidden hFinite hForbidden f hf d
    (by decide) hRootInSeam hZeroRightCount
    hRootImageInjective hExteriorOriginal

end AllThoseRamseyClasses.Lifts
