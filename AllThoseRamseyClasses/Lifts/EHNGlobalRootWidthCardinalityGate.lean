import AllThoseRamseyClasses.Lifts.EHNOriginalGlobalCollisionProfileFirewall
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Track D: a selected root wider than the finite common seam CANNOT be injected

The original root-injective 2019 global canonical lift requires
each added piece-class relation to have a distinct ordered target
root tuple. On a genuine finite common native old root X, no such
tuple of width n can exist if n exceeds the CARDINALITY of X.

This rules out an entire possible source-root repair strategy:
when a genuine forbidden geometric piece has root width greater
than the complete finite common root, no EHN map into the actual
target can realize that piece inside the common seam with
injective root coordinates, regardless of the choice of map,
even after changing its original source coordinates.

Hence a printed original canonical class relation can transfer
the piece across the two ambient side witnesses ONLY if its
positive width satisfies n <= |X|. At larger widths, both sides'
canonical predicate is FALSE on every root tuple, and the common
profile agreement is vacuous for that symbol on X.

This is a true numerical necessary condition for any proof of the
original source-root flip. It does not contradict strong AP or
replace the genuine collision-tolerant forbidden-source repair.
The folded auxiliary lift is not substituted for the original one.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- There is no injective ordered native root tuple of width n
in a common root with fewer than n original vertices. -/
theorem noInjectiveRootTuple_above_finiteRootCard
    {UX : Type} [Fintype UX] {n : ℕ}
    (hOver : Fintype.card UX < n)
    (xs : Fin n → UX) :
    ¬ Function.Injective xs := by
  intro hInjective
  have hBound : n ≤ Fintype.card UX := by
    simpa using Fintype.card_le_of_injective xs hInjective
  omega

/-- Above the size of a finite complete common FULL native
root X, EVERY ORIGINAL global canonical added relation of the
corresponding root width is FALSE on every tuple in X in BOTH
ambient native witnesses, without using maximality or even
their mutual profile compatibility. -/
theorem originalGlobalCanonical_overwideRoot_relationFalseBoth
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB : Type} [Fintype UX]
    {X : Structure L UX}
    {A : Structure L UA} {B : Structure L UB}
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B)
    (s : GlobalFunctionalPieceSymbol F)
    (hOver : Fintype.card UX < globalFunctionalPieceArity F s)
    (xs : Fin (globalFunctionalPieceArity F s) → UX) :
    ¬ (globalFunctionalCanonicalLift F A).rel
      (.inr s) (iA ∘ xs) ∧
    ¬ (globalFunctionalCanonicalLift F B).rel
      (.inr s) (iB ∘ xs) := by
  have hColl :=
    noInjectiveRootTuple_above_finiteRootCard hOver xs
  have hVacuous :=
    originalGlobalCanonical_collidedCommonRoot_profileVacuous
      F iA iB s xs hColl
  exact ⟨hVacuous.1, hVacuous.2.1⟩

/-- Source-matched cardinality obstruction: if the actual ordered
source root of any genuine geometric forbidden piece has more
vertices than the finite target common FULL root, then its image
under ANY original weak forbidden-source map whose root image
lies entirely in that common root is necessarily NONINJECTIVE.

No assumption about EHN structure, source irreducibility or
family image closure is needed. In particular replacing the
map alone cannot make the ordered root injective while keeping
the source root width and its entire image inside the same X. -/
theorem geometricForbiddenRootImage_noninjective_of_width_gt_commonRootCard
    {V UX UT : Type} [Fintype UX]
    (Source : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (Root : Structure L UX)
    (Target : Structure L UT)
    (jRoot : Structure.Embedding Root Target)
    (f : V → UT)
    (hAllRoot : ∀ i : Fin n,
      f (d.roots i) ∈ Set.range jRoot)
    (hOver : Fintype.card UX < n) :
    ¬ Function.Injective (fun i : Fin n => f (d.roots i)) := by
  classical
  let xs : Fin n → UX :=
    fun i => Classical.choose (hAllRoot i)
  have hCoords : ∀ i : Fin n,
      f (d.roots i) = jRoot (xs i) :=
    fun i => Classical.choose_spec (hAllRoot i)
  intro hInjective
  have hXsInjective : Function.Injective xs := by
    intro a b hab
    apply hInjective
    calc
      f (d.roots a) = jRoot (xs a) := hCoords a
      _ = jRoot (xs b) := congrArg jRoot.toFun hab
      _ = f (d.roots b) := (hCoords b).symm
  exact (noInjectiveRootTuple_above_finiteRootCard
    hOver xs) hXsInjective

/-- Actual original forbidden-piece version: for any genuine
geometric forbidden source with root wider than the finite
common root, any weak source map factoring its ordered roots
through that common root has a collided image, so the ORIGINAL
global selected piece-class relation is absent from the first
ambient witness. In fact no positive relation of this width
can hold on ANY common-root tuple in EITHER witness. -/
theorem originalGeometric_overwideRoot_cannotWitnessCommonCanonicalRelation
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V UX UA UB : Type} [Fintype UX]
    (Source : Structure L V)
    (hFinite : Finite V)
    (hForbidden : F Source)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (hn : 0 < n)
    (hOver : Fintype.card UX < n)
    {X : Structure L UX}
    {A : Structure L UA} {B : Structure L UB}
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B)
    (fA : V → UA)
    (hRoot : ∀ i : Fin n,
      fA (d.roots i) ∈ Set.range iA) :
    ¬ Function.Injective (fun i : Fin n => fA (d.roots i)) ∧
    (∀ xs : Fin n → UX,
      ¬ (globalFunctionalCanonicalLift F A).rel
        (.inr (geometricGlobalPieceSymbol
          F Source hFinite hForbidden d hn)) (iA ∘ xs) ∧
      ¬ (globalFunctionalCanonicalLift F B).rel
        (.inr (geometricGlobalPieceSymbol
          F Source hFinite hForbidden d hn)) (iB ∘ xs)) := by
  have hColl :=
    geometricForbiddenRootImage_noninjective_of_width_gt_commonRootCard
      Source d X A iA fA hRoot hOver
  constructor
  · exact hColl
  · intro xs
    exact originalGlobalCanonical_overwideRoot_relationFalseBoth
      F iA iB
      (geometricGlobalPieceSymbol F Source hFinite hForbidden d hn)
      (by simpa using hOver) xs

/-- POSITIVE numerical width bound for any original canonical
piece-class relation actually holding on the image of a finite
common FULL old root. It is a theorem about TRUE positive
relations, not an assumed width restriction on the signature. -/
theorem originalGlobalCanonical_positiveCommonRoot_width_le_card
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA : Type} [Fintype UX]
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A)
    (s : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F s) → UX)
    (hPositive : (globalFunctionalCanonicalLift F A).rel
      (.inr s) (iA ∘ xs)) :
    globalFunctionalPieceArity F s ≤ Fintype.card UX := by
  by_contra hNot
  have hOver : Fintype.card UX < globalFunctionalPieceArity F s := by
    omega
  have hNoInj : ¬ Function.Injective xs :=
    noInjectiveRootTuple_above_finiteRootCard hOver xs
  have hNoImageInj : ¬ Function.Injective (iA ∘ xs) := by
    intro hInj
    apply hNoInj
    intro a b hab
    exact hInj (congrArg iA.toFun hab)
  exact (originalGlobalCanonical_addedRelation_false_of_noninjective
    F A s (iA ∘ xs) hNoImageInj) hPositive

/-- Any GENUINELY INJECTIVE forbidden-source map whose selected
geometric separator root lies in a finite target seam must use
at MOST as many distinct source roots as the seam has vertices.

Thus the injective-replacement branch of the printed tuple-image
closure automatically satisfies the numeric prerequisite for
an ORIGINAL canonical piece relation. This does not show that
an arbitrary noninjective forbidden EHN witness admits that
replacement or that Claim 2 succeeds. -/
theorem injectiveForbiddenMap_selectedRootWidth_le_commonRootCard
    {V UX UT : Type} [Fintype UX]
    (Source : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (Root : Structure L UX)
    (Target : Structure L UT)
    (jRoot : Structure.Embedding Root Target)
    (f : V → UT)
    (hf : Function.Injective f)
    (hAllRoot : ∀ i : Fin n,
      f (d.roots i) ∈ Set.range jRoot) :
    n ≤ Fintype.card UX := by
  by_contra hNot
  have hOver : Fintype.card UX < n := by omega
  have hNoInj :=
    geometricForbiddenRootImage_noninjective_of_width_gt_commonRootCard
      Source d Root Target jRoot f hAllRoot hOver
  apply hNoInj
  intro a b hab
  exact d.roots_injective (hf hab)

end AllThoseRamseyClasses.Lifts
