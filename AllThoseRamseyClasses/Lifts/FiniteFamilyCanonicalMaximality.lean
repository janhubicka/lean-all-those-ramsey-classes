import AllThoseRamseyClasses.Lifts.FiniteNamedCommonComponentLift

/-!
# Monotone finite-family canonical component lifts and maximal witnesses

This is the maximal-witness interface for the ALTERNATIVE finite-named-
family all-closed-component folded lift. An old full embedding preserves
positive canonical component predicates (including folded root tuples),
but it need NOT reflect them: new witnesses can appear in a larger
structure.

We isolate the exact condition "maximal along X" used by the Section 3
amalgamation argument and prove its stability through allowed extensions.
Two maximal witnesses induce the same full component profile on X if
they embed compatibly into one common ALLOWED extension.

The existence of maximal witnesses and the existence of the common
allowed amalgam are separate mathematical obligations. In particular
the condition "D is allowed" below is NOT inferred from its being a
free amalgam. The 2019 arbitrary regular-family result remains open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Positive canonical component relations are monotone along full
OLD-language embeddings. This holds for COLLIDING root images because
the added predicate records a weak EHN rooted realization, not an
injective root-image tuple. No reflection is claimed. -/
theorem finiteNamedComponentCanonical_relation_map_embedding
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UA UB : Type}
    {A : Structure L UA} {B : Structure L UB}
    (e : Structure.Embedding A B)
    (tag : Family.ComponentTag)
    (xs : Fin (tag.width Family) → UA)
    (h : (finiteNamedClosedComponentFoldedLift Family A).rel
      (.inr tag) xs) :
    (finiteNamedClosedComponentFoldedLift Family B).rel
      (.inr tag) (e ∘ xs) := by
  change FunctionalRootRealization
    (tag.pattern Family) B (e ∘ xs)
  exact FunctionalRootRealization.map_embedding
    (tag.pattern Family) xs e h

/-- A canonical finite-family tagged lift is maximal along the
designated full old substructure X if ALL further K-extensions preserve
the COMPLETE component relation profile of X. No maximality of the
ambient A away from X is required.

K will normally be the class avoiding the finite forbidden family.
The definition does not silently assume hereditary or amalgamation
properties of K. -/
def FiniteNamedCanonicalMaximalAlong
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (K : ∀ {W : Type}, Structure L W → Prop)
    {UX UA : Type}
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A) : Prop :=
  ∀ {UC : Type} (C : Structure L UC), K C →
    (e : Structure.Embedding A C) →
    ∀ (tag : Family.ComponentTag)
      (xs : Fin (tag.width Family) → UX),
      (finiteNamedClosedComponentFoldedLift Family C).rel
        (.inr tag) (e ∘ iA ∘ xs) ↔
      (finiteNamedClosedComponentFoldedLift Family A).rel
        (.inr tag) (iA ∘ xs)

/-- Maximality is equivalent to the NO-NEW-component-witness
condition: forward preservation comes for free from old full
embeddings, so only reflection in arbitrary K-extensions must be
checked. This is the useful direction for a finite profile
maximization construction. -/
theorem finiteNamedCanonicalMaximalAlong_iff_no_new
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (K : ∀ {W : Type}, Structure L W → Prop)
    {UX UA : Type}
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A) :
    FiniteNamedCanonicalMaximalAlong Family K iA ↔
      (∀ {UC : Type} (C : Structure L UC), K C →
        (e : Structure.Embedding A C) →
        ∀ (tag : Family.ComponentTag)
          (xs : Fin (tag.width Family) → UX),
          (finiteNamedClosedComponentFoldedLift Family C).rel
            (.inr tag) (e ∘ iA ∘ xs) →
          (finiteNamedClosedComponentFoldedLift Family A).rel
            (.inr tag) (iA ∘ xs)) := by
  constructor
  · intro hmax UC C hC e tag xs h
    exact (hmax C hC e tag xs).mp h
  · intro hnonew UC C hC e tag xs
    constructor
    · exact hnonew C hC e tag xs
    · intro hA
      have hB := finiteNamedComponentCanonical_relation_map_embedding
        Family e tag (iA ∘ xs) hA
      convert hB using 1

/-- Maximality persists after any allowed FULL extension: the
composition of that extension with a further K-extension remains
an extension of the original maximal witness. -/
theorem FiniteNamedCanonicalMaximalAlong.of_allowed_extension
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (K : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UD : Type}
    {X : Structure L UX}
    {A : Structure L UA} {D : Structure L UD}
    (iA : Structure.Embedding X A)
    (hmax : FiniteNamedCanonicalMaximalAlong Family K iA)
    (hD : K D)
    (eAD : Structure.Embedding A D) :
    FiniteNamedCanonicalMaximalAlong Family K (eAD.comp iA) := by
  intro UC C hC eDC tag xs
  have hCfromA := hmax C hC (eDC.comp eAD) tag xs
  have hDfromA := hmax D hD eAD tag xs
  have hComposed :
      ((eDC.comp eAD) ∘ iA ∘ xs) =
        (eDC ∘ (eAD.comp iA) ∘ xs) := by
    funext j
    rfl
  have hRoot :
      (eAD ∘ iA ∘ xs) = ((eAD.comp iA) ∘ xs) := by
    funext j
    rfl
  calc
    (finiteNamedClosedComponentFoldedLift Family C).rel
        (.inr tag) (eDC ∘ (eAD.comp iA) ∘ xs) ↔
      (finiteNamedClosedComponentFoldedLift Family C).rel
        (.inr tag) ((eDC.comp eAD) ∘ iA ∘ xs) := by
          exact Iff.of_eq (congrArg
            (fun t : Fin (tag.width Family) → UC =>
              (finiteNamedClosedComponentFoldedLift Family C).rel
                (.inr tag) t) hComposed.symm)
    _ ↔ (finiteNamedClosedComponentFoldedLift Family A).rel
        (.inr tag) (iA ∘ xs) := hCfromA
    _ ↔ (finiteNamedClosedComponentFoldedLift Family D).rel
        (.inr tag) (eAD ∘ iA ∘ xs) := hDfromA.symm
    _ ↔ (finiteNamedClosedComponentFoldedLift Family D).rel
        (.inr tag) ((eAD.comp iA) ∘ xs) := by
          exact Iff.of_eq (congrArg
            (fun t : Fin (tag.width Family) → UD =>
              (finiteNamedClosedComponentFoldedLift Family D).rel
                (.inr tag) t) hRoot)

/-- Two maximal witnesses agreeing as old structures on X have
identical EVERY-component canonical relation profiles on X as soon
as they are placed compatibly in ONE allowed common extension D.

The existence of D is an explicit assumption, not a hidden use of
the missing strong-amalgamation theorem. -/
theorem finiteNamedMaximalLifts_agree_in_allowed_common_extension
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (K : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UB UD : Type}
    {X : Structure L UX} {A : Structure L UA}
    {B : Structure L UB} {D : Structure L UD}
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B)
    (hMaxA : FiniteNamedCanonicalMaximalAlong Family K iA)
    (hMaxB : FiniteNamedCanonicalMaximalAlong Family K iB)
    (hD : K D)
    (eA : Structure.Embedding A D)
    (eB : Structure.Embedding B D)
    (hCommon : ∀ x : UX, eA (iA x) = eB (iB x)) :
    FiniteNamedComponentLiftsAgreeOn Family iA iB := by
  intro tag xs
  have hA := hMaxA D hD eA tag xs
  have hB := hMaxB D hD eB tag xs
  have hTuple :
      (eA ∘ iA ∘ xs) = (eB ∘ iB ∘ xs) := by
    funext j
    exact hCommon (xs j)
  calc
    (finiteNamedClosedComponentFoldedLift Family A).rel
        (.inr tag) (iA ∘ xs) ↔
      (finiteNamedClosedComponentFoldedLift Family D).rel
        (.inr tag) (eA ∘ iA ∘ xs) := hA.symm
    _ ↔ (finiteNamedClosedComponentFoldedLift Family D).rel
        (.inr tag) (eB ∘ iB ∘ xs) := by
          exact Iff.of_eq (congrArg
            (fun t : Fin (tag.width Family) → UD =>
              (finiteNamedClosedComponentFoldedLift Family D).rel
                (.inr tag) t) hTuple)
    _ ↔ (finiteNamedClosedComponentFoldedLift Family B).rel
        (.inr tag) (iB ∘ xs) := hB

end AllThoseRamseyClasses.Lifts
