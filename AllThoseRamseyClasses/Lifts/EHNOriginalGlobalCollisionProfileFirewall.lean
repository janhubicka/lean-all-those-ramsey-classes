import AllThoseRamseyClasses.Lifts.CommonGlobalCanonicalLift
import AllThoseRamseyClasses.Lifts.GeometricGlobalPieceSymbol

/-!
# Track D: original root-injective canonical relations are blind at collided roots

The original 2019 global functional canonical F-lift defines EVERY
added piece-class relation only on INJECTIVE ordered root tuples.
Consequently, when an original weak forbidden-source map identifies
two DISTINCT source separator-root coordinates, its own genuine
selected geometric piece-class relation is FALSE at that root
tuple in BOTH compatible original canonical side lifts.

Indeed EVERY positive-width added class relation is false on a
collapsed common-root tuple. The full canonical profile agreement
there is consequently FALSE ↔ FALSE. It does not, by itself,
supply a positive replacement piece.

These are kernel-checkable proof-control safeguards for the missing
collision-tolerant original 2019 Claim 1/Claim 2 source flip.
They are NOT counterexamples to strong amalgamation. The auxiliary
FOLDED canonical lift may treat collided tuples differently;
the theorems here concern the ORIGINAL injective-root language.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every ORIGINAL global added piece-class relation is false on
a noninjective ordered target tuple, independent of the ambient
native functional structure and the forbidden family. -/
theorem originalGlobalCanonical_addedRelation_false_of_noninjective
    (F : ∀ {W : Type}, Structure L W → Prop)
    {W : Type} (A : Structure L W)
    (s : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F s) → W)
    (hColl : ¬ Function.Injective xs) :
    ¬ (globalFunctionalCanonicalLift F A).rel (.inr s) xs := by
  intro hPositive
  exact hColl
    (globalFunctionalCanonicalRelation_injective F A s xs hPositive)

/-- When a common-root tuple COLLAPSES, it supports NO ORIGINAL
positive canonical piece-class relation in EITHER ambient full
side, and their common-root profile equivalence is automatic
for that tuple. This does not invoke maximality or an existing
full common lifted structure: it is a consequence of the
definition of the original root-injective lifted relations. -/
theorem originalGlobalCanonical_collidedCommonRoot_profileVacuous
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB : Type}
    {X : Structure L UX}
    {A : Structure L UA} {B : Structure L UB}
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B)
    (s : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F s) → UX)
    (hColl : ¬ Function.Injective xs) :
    (¬ (globalFunctionalCanonicalLift F A).rel (.inr s) (iA ∘ xs)) ∧
    (¬ (globalFunctionalCanonicalLift F B).rel (.inr s) (iB ∘ xs)) ∧
    ((globalFunctionalCanonicalLift F A).rel (.inr s) (iA ∘ xs) ↔
     (globalFunctionalCanonicalLift F B).rel (.inr s) (iB ∘ xs)) := by
  have hAInjFalse : ¬ Function.Injective (iA ∘ xs) := by
    intro hInj
    apply hColl
    intro j k h
    exact hInj (congrArg iA.toFun h)
  have hBInjFalse : ¬ Function.Injective (iB ∘ xs) := by
    intro hInj
    apply hColl
    intro j k h
    exact hInj (congrArg iB.toFun h)
  have hAFalse :=
    originalGlobalCanonical_addedRelation_false_of_noninjective
      F A s (iA ∘ xs) hAInjFalse
  have hBFalse :=
    originalGlobalCanonical_addedRelation_false_of_noninjective
      F B s (iB ∘ xs) hBInjFalse
  refine ⟨hAFalse, hBFalse, ?_⟩
  constructor
  · intro h
    exact False.elim (hAFalse h)
  · intro h
    exact False.elim (hBFalse h)

/-- Source-matched ORIGINAL selected forbidden geometric piece
instance. Its SOURCE root tuple is injectively enumerated, but
if the weak source map fA into A COLLAPSES the root images
lying in the common embedded root X, the selected ORIGINAL
global class relation is absent in BOTH side witnesses.

The matching class-profile equivalence on that tuple is therefore
vacuous. This is precisely why a common original canonical lift
does not, by itself, justify a selected-Q flip at colliding roots.
No EHN assumption is needed for this negative root-image fact. -/
theorem originalGeometricCollidedRoot_symbolFalse_onBothWitnesses
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V UX UA UB : Type}
    (Source : Structure L V)
    (hFinite : Finite V) (hForbidden : F Source)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (hn : 0 < n)
    {X : Structure L UX}
    {A : Structure L UA} {B : Structure L UB}
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B)
    (fA : V → UA)
    (xsX : Fin n → UX)
    (hCoords : ∀ i : Fin n,
      fA (d.roots i) = iA (xsX i))
    (hColl : ¬ Function.Injective
      (fun i : Fin n => fA (d.roots i))) :
    (¬ (globalFunctionalCanonicalLift F A).rel
      (.inr (geometricGlobalPieceSymbol
        F Source hFinite hForbidden d hn)) (iA ∘ xsX)) ∧
    (¬ (globalFunctionalCanonicalLift F B).rel
      (.inr (geometricGlobalPieceSymbol
        F Source hFinite hForbidden d hn)) (iB ∘ xsX)) := by
  have hXColl : ¬ Function.Injective xsX := by
    intro hInjective
    apply hColl
    intro j k hjk
    have hEqA : iA (xsX j) = iA (xsX k) := by
      calc
        iA (xsX j) = fA (d.roots j) := (hCoords j).symm
        _ = fA (d.roots k) := hjk
        _ = iA (xsX k) := hCoords k
    exact hInjective (iA.injective hEqA)
  have hAll :=
    originalGlobalCanonical_collidedCommonRoot_profileVacuous
      F iA iB
      (geometricGlobalPieceSymbol
        F Source hFinite hForbidden d hn) xsX hXColl
  exact ⟨hAll.1, hAll.2.1⟩

end AllThoseRamseyClasses.Lifts
