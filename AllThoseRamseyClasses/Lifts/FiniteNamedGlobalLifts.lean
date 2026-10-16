import AllThoseRamseyClasses.Lifts.RegularLiftPrecompactness

/-!
# Finite named-carrier functional lifts under regularity

The previous finite-support theorem bounds the complete choice of
additional relation predicates on one finite carrier. Here we
package those choices as ACTUAL expanded functional structures
whose old-language shadow is a fixed structure A, not just as
tables of Boolean observations.

Every permitted expansion is obtained by interpreting the new
relations using distinct-root-only data, and leaving each old
relation/function interpretation EXACTLY as in A. Finite many such
relation tables therefore give finitely many named-carrier lifts.
In particular the canonical functional lift is one of them.

This is the finite-labelled version of the 2019 precompactness
assertion. From this one obtains finite isomorphism TYPES of
expansions of each finite old structure, after choosing a fixed
representative carrier and transporting expansions by old-language
isomorphisms. The transport/renaming lemma is separate.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u

/-- All exact named-carrier expansions of A obtained by adding
distinct-root-only global piece-class relations while leaving the
entire old functional structure unchanged. -/
def NamedGlobalLiftOptions
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V : Type} (A : Structure L V) :=
  {X : Structure (globalFunctionalPieceLanguage F) V //
    ∃ E : DistinctRootExtraData
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) V,
      X = functionalWithExtraBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F)
        A E.1}

/-- Under regularity the entire TYPE of named-carrier functional
lifts (not only their new relation tables) is finite. -/
theorem finite_namedGlobalLiftOptions_of_regular
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V : Type} (A : Structure L V)
    [Fintype V]
    (hRegular : GlobalFunctionalPieceRegular F) :
    Finite (NamedGlobalLiftOptions F A) := by
  classical
  let Data :=
    DistinctRootExtraData
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) V
  letI : Finite Data :=
    finite_globalDistinctRootExtraData_of_regular F V hRegular
  let realize : Data → NamedGlobalLiftOptions F A :=
    fun E =>
      ⟨functionalWithExtraBig L
          (GlobalFunctionalPieceSymbol F)
          (globalFunctionalPieceArity F) A E.1,
        ⟨E, rfl⟩⟩
  apply Finite.of_surjective realize
  rintro ⟨X, hX⟩
  obtain ⟨E, hE⟩ := hX
  refine ⟨E, ?_⟩
  apply Subtype.ext
  exact hE.symm

/-- Every named lift option has exactly A as its functional shadow,
including ALL old relation and function values. -/
theorem namedGlobalLiftOptions_shadow
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V : Type} (A : Structure L V)
    (X : NamedGlobalLiftOptions F A) :
    functionalShadowBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F)
      X.1 = A := by
  obtain ⟨E, hE⟩ := X.2
  rw [hE]
  exact functionalShadowBig_withExtra L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F)
    A E.1

/-- Every extra tuple in a named lift option has pairwise distinct
vertices, even if its signature arity is larger than the carrier. -/
theorem namedGlobalLiftOptions_distinct
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V : Type} (A : Structure L V)
    (X : NamedGlobalLiftOptions F A)
    (i : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F i) → V)
    (h : X.1.rel (.inr i) xs) :
    Function.Injective xs := by
  obtain ⟨E, hE⟩ := X.2
  rw [hE] at h
  exact E.2 i xs h

/-- In particular the actual GLOBAL canonical functional lift of
A is one of the finitely many labelled options for A. -/
def namedGlobalCanonicalLift
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V : Type} (A : Structure L V) :
    NamedGlobalLiftOptions F A where
  val := globalFunctionalCanonicalLift F A
  property := ⟨globalCanonicalDistinctRootExtraData F A, rfl⟩

end AllThoseRamseyClasses.Lifts
