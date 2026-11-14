import AllThoseRamseyClasses.Lifts.GeometricIrreducibleRootImage

/-!
# Track D: root injectivity from pairwise irreducible source-test coverage

An ACTUAL original EHN map is a weak positive old-language map
which restricts to a FULL embedding on each genuine irreducible
source test. Hence two distinct source vertices whose target
images coincide can never lie together in one such FULL test.

For geometric closed separator roots, the entire induced root
need NOT be irreducible to ensure root-image injectivity:
it suffices that every pair of distinct roots occurs together
in SOME irreducible FULL source test, potentially much larger
than the selected root. This weakens the existing sufficient
condition in GeometricIrreducibleRootImage.lean and discharges
the ACTUAL root-injectivity gate of original Claim 1 for this
larger, explicitly checkable class of source geometric pieces.

This DOES NOT injectivize an arbitrary EHN map, repair
uncovered pairs of source roots, build a new forbidden
witness, or close original Claim 2/strong amalgamation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every pair of distinct source vertices inside S belongs to
a common FULL irreducible source test. The test may include
vertices outside S; no assumption that S is closed or globally
irreducible is made. -/
def PairwiseIrreducibleSourceTestCover
    {V : Type} (Source : Structure L V) (S : Set V) : Prop :=
  ∀ (a : V), a ∈ S →
    ∀ (b : V), b ∈ S → a ≠ b →
      ∃ (X : Type) (E : Structure L X),
        E.Irreducible ∧
        ∃ e : Structure.Embedding E Source,
          ∃ x y : X, e x = a ∧ e y = b

/-- Genuinely COLLIDING DISTINCT original source vertices of an
EHN map cannot be covered by the same FULL native irreducible
source test. This uses target FULL-test injectivity, not an
unjustified global injectivity assumption on the EHN map. -/
theorem ehn_collidingSourcePair_not_in_jointIrreducibleTest
    {V UT : Type}
    (Source : Structure L V) (Target : Structure L UT)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (a b : V) (hab : a ≠ b) (hSame : f a = f b) :
    ¬ ∃ (X : Type) (E : Structure L X),
      E.Irreducible ∧
      ∃ e : Structure.Embedding E Source,
        ∃ x y : X, e x = a ∧ e y = b := by
  rintro ⟨X, E, hIr, e, x, y, hx, hy⟩
  obtain ⟨ge, hge⟩ := hf.2 E hIr e
  have hTargetEq : ge x = ge y := by
    calc
      ge x = f (e x) := hge x
      _ = f a := congrArg f hx
      _ = f b := hSame
      _ = f (e y) := (congrArg f hy).symm
      _ = ge y := (hge y).symm
  have hSourceEq : e x = e y :=
    congrArg e (ge.injective hTargetEq)
  exact hab (hx.symm.trans (hSourceEq.trans hy))

/-- An ACTUAL native EHN map is injective on any source set
whose distinct pairs are jointly FULL irreducible-test-covered.
No finiteness, closedness, or global-source irreducibility. -/
theorem ehn_injOn_of_pairwiseIrreducibleSourceTestCover
    {V UT : Type}
    (Source : Structure L V) (Target : Structure L UT)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (S : Set V) (hCover : PairwiseIrreducibleSourceTestCover Source S) :
    Set.InjOn f S := by
  intro a ha b hb hEq
  by_contra hDistinct
  exact (ehn_collidingSourcePair_not_in_jointIrreducibleTest
    Source Target f hf a b hDistinct hEq)
    (hCover a ha b hb hDistinct)

/-- If the entire native closed induced root is irreducible,
then it supplies a common FULL irreducible test for every
distinct root pair. Thus the pairwise-cover hypothesis is
at least as weak as the previously verified irreducible-root
hypothesis. -/
theorem pairwiseSourceTestCover_of_irreducibleClosedSet
    {V : Type} (Source : Structure L V) (S : Set V)
    (hClosed : Source.IsClosed S)
    (hIr : (Source.induce S hClosed).Irreducible) :
    PairwiseIrreducibleSourceTestCover Source S := by
  intro a ha b hb _hab
  exact ⟨S, Source.induce S hClosed, hIr,
    Source.inclusion S hClosed, ⟨a, ha⟩, ⟨b, hb⟩, rfl, rfl⟩

/-- Actual geometric ordered separator-root images are
injective whenever every distinct pair of ORIGINAL root
vertices admits a joint FULL irreducible source test. The
chosen native geometric root itself may be reducible. -/
theorem geometricRootImage_injective_of_pairwiseSourceTests
    {V UT : Type}
    (Source : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (hCover : PairwiseIrreducibleSourceTestCover
      Source (Set.range d.roots)) :
    Function.Injective (fun i : Fin n => f (d.roots i)) := by
  have hInj : Set.InjOn f (Set.range d.roots) :=
    ehn_injOn_of_pairwiseIrreducibleSourceTestCover
      Source Target f hf (Set.range d.roots) hCover
  intro i j hEq
  have hi : d.roots i ∈ Set.range d.roots := ⟨i, rfl⟩
  have hj : d.roots j ∈ Set.range d.roots := ⟨j, rfl⟩
  exact d.roots_injective (hInj hi hj hEq)

/-- An ACTUAL strong Claim 1 consequence under a weaker source
hypothesis than irreducibility of the whole native closed root:
pairwise joint test coverage of its ordered separator vertices.

The root-image injection is DERIVED from the verified EHN map,
then the existing original-global-canonical-lift Claim 1 argument
produces a real source vertex of the selected component mapped
right-exclusively.

The root's pairwise test coverage is intentionally explicit:
it is NOT implied by connectedness of the forbidden source. -/
theorem minimalGlobalWitness_pieceMeetsRight_of_rootPairwiseSourceTests
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
    (hCover : PairwiseIrreducibleSourceTestCover
      w.source (Set.range d.roots)) :
    ∃ z : w.Carrier,
      z ∈ functionalComponentFrom w.source
        (Set.range d.roots) d.left ∧
      z ∈ weakFreeRightPart
        (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget := by
  exact minimalGlobalWitness_pieceMeetsRight_of_rootInjective
    F hFiniteF Target Left Right jLeft jRight
    X iLeft iRight hTargetFree hCommon w hMin
    d hn hRoots hLeft
    (geometricRootImage_injective_of_pairwiseSourceTests
      w.source d Target w.toTarget w.homEmbedding hCover)

end AllThoseRamseyClasses.Lifts
