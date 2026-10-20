import AllThoseRamseyClasses.Lifts.GlobalOriginalClaim1OneSided
import AllThoseRamseyClasses.Lifts.GeometricPieceRootChart

/-!
# Genuine sufficient conditions for injectivity of a geometric root image

The original root-injective global lift requires an injective ordered
root IMAGE to interpret its canonical extra relation. A weak EHN
homomorphism-embedding does not generally imply this. But the
irreducible-test clause of the EHN definition does imply it whenever
the entire CLOSED separator root is irreducible in the full native
functional language: its full inclusion into the forbidden source
then maps by an actual FULL embedding into the target.

The proof uses the source's exact induced closed-root structure,
its actual FULL inclusion, and the EHN irreducible test. It does not
replace a weak image by an incorrectly assumed full induced image.

In particular root images of WIDTH ONE are always injective for
purely set-theoretic reasons. These supply genuine, restricted
nonconditional instances of the previously verified Claim 1
one-sided exclusion, but they do NOT cover reducible separators
with colliding root images or complete the original Section 3.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- If the entire induced CLOSED root of a geometric piece is
irreducible in the NATIVE function-language sense, then an EHN weak
homomorphism-embedding is injective on its distinct ordered source
roots. This does not assert the original weak map is globally
injective. -/
theorem geometricRootImage_injective_of_irreducibleClosedRoot
    {V UT : Type}
    (Source : Structure L V)
    {n : ℕ}
    (d : GeometricFunctionalPieceData Source n)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (hRootIrreducible :
      (Source.induce (Set.range d.roots) d.minimal.1).Irreducible) :
    Function.Injective (fun i : Fin n => f (d.roots i)) := by
  let R : Set V := Set.range d.roots
  let Root : Structure L R := Source.induce R d.minimal.1
  let iRoot : Structure.Embedding Root Source :=
    Source.inclusion R d.minimal.1
  obtain ⟨g, hg⟩ := hf.2 Root hRootIrreducible iRoot
  intro i j hEq
  let ri : R := ⟨d.roots i, ⟨i, rfl⟩⟩
  let rj : R := ⟨d.roots j, ⟨j, rfl⟩⟩
  have hgi : g ri = f (d.roots i) := hg ri
  have hgj : g rj = f (d.roots j) := hg rj
  have hG : ri = rj := g.injective (hgi.trans (hEq.trans hgj.symm))
  exact d.roots_injective (congrArg Subtype.val hG)

/-- A one-coordinate geometric root has an injective image under
ANY map, even without a homomorphism condition. -/
theorem geometricRootImage_injective_widthOne
    {V UT : Type} (Source : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (f : V → UT)
    (hn : n = 1) :
    Function.Injective (fun i : Fin n => f (d.roots i)) := by
  subst n
  intro i j _
  exact Subsingleton.elim i j

/-- Actual conditional Claim 1 becomes a complete one-sided
exclusion for any POSITIVE geometric piece whose closed root is
irreducible, without assuming injectivity of its image as an
independent extra hypothesis. The source may still be noninjective
away from the separator. -/
theorem minimalGlobalWitness_pieceMeetsRight_of_irreducibleRoot
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {UX UA UB UT : Type}
    (Target : Structure L UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (w : ForbiddenEHNWitness F Target)
    (hMin : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft) ≤
        v.sourceSupportCount (fullFreeLeftExclusiveTarget iLeft jLeft))
    {n : ℕ}
    (d : GeometricFunctionalPieceData w.source n)
    (hn : 0 < n)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget)
    (hLeft : d.left.1 ∈
      weakFreeLeftPart (sL := iLeft) (iL := jLeft) w.toTarget)
    (hRootIrreducible :
      (w.source.induce (Set.range d.roots) d.minimal.1).Irreducible) :
    ∃ z : w.Carrier,
      z ∈ functionalComponentFrom w.source
        (Set.range d.roots) d.left ∧
      z ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget := by
  exact minimalGlobalWitness_pieceMeetsRight_of_rootInjective
    F hFiniteF Target Left Right jLeft jRight
    X iLeft iRight hTargetFree hCommon w hMin
    d hn hRoots hLeft
    (geometricRootImage_injective_of_irreducibleClosedRoot
      w.source d Target w.toTarget w.homEmbedding hRootIrreducible)

end AllThoseRamseyClasses.Lifts
