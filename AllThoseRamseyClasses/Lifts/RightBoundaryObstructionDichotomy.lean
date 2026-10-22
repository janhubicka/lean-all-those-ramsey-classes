import AllThoseRamseyClasses.Lifts.WeakRightBoundaryCoverage

/-!
# Two explicit local obstructions at a right-support-minimal forbidden witness

The verified arbitrary-width right-component flip needs only
(1) an opposite left component whose full generated boundary
covers the right-component boundary T, and
(2) injective images of the vertices of T.

At an actual forbidden weak EHN witness minimizing RIGHT-exclusive
SOURCE support, these two properties cannot coexist. The next
theorem produces a CONCRETE witness to their failure:

* EITHER two different source vertices of T have the same
  image under the weak target map,
* OR some actual vertex of T is NOT in the full generated
  boundary of the opposite component after deleting T.

This is an exhaustive source-attached dichotomy for EACH chosen
right-exclusive component x and EACH left-exclusive vertex a,
without choosing an outer mixed piece. If the weak map is
injective on the full common-root preimage, the second alternative
is forced, so we get an ACTUAL uncovered boundary vertex.

No source quotient, global injection or artificial graph-only
closure replaces the original native partial functions.
This does not prove that the coverage defect is impossible.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- At a RIGHT-support minimum and for EVERY fixed opposite-side
pair (right-component vertex x, left-exclusive vertex a),
there is either a genuine collision of two vertices in the
generated right boundary or a genuinely uncovered right
boundary vertex in the a-component after deleting that boundary.

The resulting y is exactly the original source vertex a,
not a new or quotient vertex. -/
theorem minimalRightWitness_boundaryCollision_or_uncovered
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
    (w : ForbiddenEHNWitness F Target)
    (hMinRight : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) ≤
        v.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight))
    (x : {z : w.Carrier // z ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
    (T : Set w.Carrier)
    (hT : T = w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget) x)))
    (hTS : T ⊆ weakFreeRootPart
      (sL := iLeft) (iL := jLeft) w.toTarget)
    (a : w.Carrier)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) w.toTarget) :
    ∃ y : {z : w.Carrier // z ∉ T},
      y.1 = a ∧
        ((∃ u v : w.Carrier,
            u ∈ T ∧ v ∈ T ∧ u ≠ v ∧ w.toTarget u = w.toTarget v) ∨
          (∃ t : w.Carrier,
            t ∈ T ∧
              t ∉ w.source.functionClosure
                (gaifmanNeighborhood w.source.graph
                  (componentFrom w.source.graph T y)))) := by
  classical
  obtain ⟨y, hYa, _hSep⟩ :=
    weakRightComponent_leftVertex_separatedByBoundary
      hFree w.toTarget w.homEmbedding
      x hxRight T hT hTS a haLeft
  by_cases hCoverage : T ⊆ w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph T y))
  · have hAllCoverage :
        ∀ y' : {z : w.Carrier // z ∉ T}, y'.1 = a →
          T ⊆ w.source.functionClosure
            (gaifmanNeighborhood w.source.graph
              (componentFrom w.source.graph T y')) := by
      intro y' hY'a
      have hEq : y' = y :=
        Subtype.ext (hY'a.trans hYa.symm)
      simpa only [hEq] using hCoverage
    have hCollision :=
      (minimalRightWitness_oppositeCoverage_forcesCollision
        F hFiniteF hConnected Target Left Right jLeft jRight
        X iLeft iRight hFree hCommon w hMinRight
        x hxRight T hT hTS a haLeft hAllCoverage).1
    exact ⟨y, hYa, Or.inl hCollision⟩
  · obtain ⟨t, htT, htMissing⟩ :
        ∃ t : w.Carrier,
          t ∈ T ∧
            t ∉ w.source.functionClosure
              (gaifmanNeighborhood w.source.graph
                (componentFrom w.source.graph T y)) :=
      Set.not_subset.mp hCoverage
    exact ⟨y, hYa, Or.inr ⟨t, htT, htMissing⟩⟩

/-- If the weak map is injective JUST on the full shared-root
preimage (possibly not anywhere else), a right-support minimum
forces an ACTUAL uncovered vertex in the generated boundary
of every right component relative to each opposite left
vertex. This is the precise remaining geometric obstruction
in the root-injective case of the printed Claim 2. -/
theorem minimalRightWitness_uncovered_of_rootInjOn
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
    (w : ForbiddenEHNWitness F Target)
    (hMinRight : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight) ≤
        v.sourceSupportCount
          (fullFreeRightExclusiveTarget iRight jRight))
    (hInjOnRoot : Set.InjOn w.toTarget
      (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget))
    (x : {z : w.Carrier // z ∉
      weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget})
    (hxRight : x.1 ∈ weakFreeRightPart
      (sL := iLeft) (iL := jLeft) (iR := jRight) w.toTarget)
    (T : Set w.Carrier)
    (hT : T = w.source.functionClosure
      (gaifmanNeighborhood w.source.graph
        (componentFrom w.source.graph
          (weakFreeRootPart (sL := iLeft) (iL := jLeft) w.toTarget) x)))
    (hTS : T ⊆ weakFreeRootPart
      (sL := iLeft) (iL := jLeft) w.toTarget)
    (a : w.Carrier)
    (haLeft : a ∈ weakFreeLeftPart
      (sL := iLeft) (iL := jLeft) w.toTarget) :
    ∃ (y : {z : w.Carrier // z ∉ T}) (t : w.Carrier),
      y.1 = a ∧ t ∈ T ∧
        t ∉ w.source.functionClosure
          (gaifmanNeighborhood w.source.graph
            (componentFrom w.source.graph T y)) := by
  obtain ⟨y, hYa, hCollision | hUncovered⟩ :=
    minimalRightWitness_boundaryCollision_or_uncovered
      F hFiniteF hConnected
      Target Left Right jLeft jRight X iLeft iRight
      hFree hCommon w hMinRight
      x hxRight T hT hTS a haLeft
  · obtain ⟨u, v, hu, hv, hDifferent, hEqual⟩ := hCollision
    exact False.elim (hDifferent
      (hInjOnRoot (hTS hu) (hTS hv) hEqual))
  · obtain ⟨t, ht, htNot⟩ := hUncovered
    exact ⟨y, t, hYa, ht, htNot⟩

end AllThoseRamseyClasses.Lifts
