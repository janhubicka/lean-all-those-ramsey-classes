import AllThoseRamseyClasses.Lifts.ForbiddenWeakWitnessMinimization
import AllThoseRamseyClasses.Lifts.FoldedCommonFlipStrictSupport
import AllThoseRamseyClasses.Lifts.GeometricPieceSideDichotomy
import AllThoseRamseyClasses.Lifts.GeometricCommonRootCoordinates

/-!
# General first geometric minimality claim for a shared FOLDED canonical lift

The 2019 proof of `lem:amalgamationstr` claims that a forbidden
source map minimizing A-only support has the following property:
EVERY genuine geometric piece rooted inside the full common-root
preimage and meeting the A-only source part must ALSO meet B-only.

The original distinct-root canonical lift does not justify this
for noninjective root-image maps. For the explicitly DIFFERENT
auxiliary FOLDED canonical lift, we have now proved all the required
building blocks:

* genuine source-piece factorization into Left if it avoids B-only;
* construction of the ordered common-root coordinate tuple from
  the actual weak source map and full witness embeddings;
* a literal forbidden-source flipped replacement into Right, which
  preserves the old complementary map and strictly decreases A-only
  SOURCE support even if root images collide;
* a minimizer among actual finite forbidden weak EHN witnesses.

This module assembles the unrestricted FIRST CLAIM for arbitrary
numbers of right-exclusive source components. It does NOT assume
the right-exclusive source part is connected. It still assumes
the existence of a common FULL FOLDED canonical lift of Left and
Right, as a separate witness. Positive root width is explicit,
as in the actual global piece-symbol index.

This is NOT the full Section 3 strong-amalgamation theorem:
the second multicomponent Claim 2 and the class-level maximal
folded witness construction remain unverified.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- FOLDED version of the COMPLETE FIRST CLAIM:
For a minimal-support finite forbidden EHN witness, every
positive-width genuine minimal-separator piece with its root
inside the exact common-root preimage and one A-only source
vertex in its selected component has a B-only vertex there too.

The original weak map and its selected root image may be
noninjective; no connectivity assumption on the B-only
source region is made. -/
theorem minimalFoldedForbiddenWitness_piece_meets_right
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W),
      F A → Finite W)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA)
    (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonFoldedGlobalCanonicalLift
      F X Left Right iLeft iRight)
    (w : ForbiddenEHNWitness F Target)
    (hMinimal : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
      v.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft))
    {n : ℕ}
    (d : GeometricFunctionalPieceData w.source n)
    (hn : 0 < n)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft)
        w.toTarget)
    (a : w.Carrier)
    (haComponent : a ∈
      functionalComponentFrom w.source
        (Set.range d.roots) d.left)
    (haLeft : a ∈
      weakFreeLeftPart (sL := iLeft) (iL := jLeft)
        w.toTarget) :
    ∃ b : w.Carrier,
      b ∈ functionalComponentFrom w.source
        (Set.range d.roots) d.left ∧
      b ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight)
        w.toTarget := by
  classical
  by_contra hNone
  have hAvoidRight : ∀ b : w.Carrier,
      b ∈ functionalComponentFrom w.source
        (Set.range d.roots) d.left →
      b ∉ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight)
        w.toTarget := by
    intro b hbC hbRight
    exact hNone ⟨b, hbC, hbRight⟩
  obtain ⟨pLeft, hpLeft, hPieceMap⟩ :=
    weakGeometricPiece_factor_left_if_no_right
      hFree w.toTarget w.homEmbedding d hRoots hAvoidRight
  have hpLeft' :
      (geometricGlobalFunctionalChart w.source d).ext.str.IsEHNHomomorphismEmbedding
        Left pLeft := hpLeft
  have hPieceMap' :
      ∀ z : (geometricGlobalFunctionalChart w.source d).ext.Carrier,
        jLeft (pLeft z) = w.toTarget z.1 := hPieceMap
  obtain ⟨xsX, hRootLeft⟩ :=
    geometricPiece_commonRootCoordinates
      w.source d Target w.toTarget X Left
      iLeft jLeft pLeft hPieceMap' hRoots
  obtain ⟨W, New, hNewForbidden, flip, hFlip, hStrict⟩ :=
    geometricFoldedCommonFullLiftFlip_strict_leftSupport
      F hFiniteF w.source w.finiteCarrier w.forbidden d hn
      Target w.toTarget w.homEmbedding
      Left Right jLeft jRight
      X iLeft iRight hFree hCommon
      pLeft hpLeft' hPieceMap' xsX hRootLeft
      a haComponent haLeft
  let replacement : ForbiddenEHNWitness F Target := {
    Carrier := W
    finiteCarrier := hFiniteF New hNewForbidden
    source := New
    forbidden := hNewForbidden
    toTarget := flip
    homEmbedding := hFlip
  }
  have hDrop :
      replacement.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) <
      w.sourceSupportCount
        (fullFreeLeftExclusiveTarget iLeft jLeft) :=
    hStrict
  exact (minimalForbiddenEHNWitness_no_strict_drop
    (fullFreeLeftExclusiveTarget iLeft jLeft)
    w hMinimal replacement) hDrop

end AllThoseRamseyClasses.Lifts
