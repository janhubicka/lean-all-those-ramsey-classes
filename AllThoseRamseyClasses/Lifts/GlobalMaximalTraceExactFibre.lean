import AllThoseRamseyClasses.Lifts.GlobalMaximalTraceAge
import AllThoseRamseyClasses.Lifts.FiniteNamedGlobalLifts

/-!
# Exact precompactness of the original regular maximal induced-trace age

The original root-INJECTIVE global canonical lift of a regular
forbidden-piece family has finitely many possible additional relation
tables over every finite old shadow. Maximal induced traces use only
these root-injective tables, and their entire original functional
shadow is fixed exactly.

We prove the missing coverage step, rather than merely bounding a
chosen subset of the age: every actual finite maximal-trace expansion
with a fixed old shadow A canonically gives a named lift option
over A. The map is injective because the old shadow is fixed and
all new relation interpretations are recorded.

Thus the type of ALL genuine maximal-trace age members over a fixed
finite allowed original A is finite and nonempty. For a hereditary K
its fibre is nonempty exactly over members of K. No globally finite
new signature, bound on piece width, strong amalgamation, or Ramsey
assumption is required.

These are statements for the original distinct-root canonical
global lift, NOT the folded all-component finite-family alternative.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every added relation of a genuine finite maximal trace uses
an INJECTIVE ordered root tuple. This is inherited from the real
global canonical relation in its full witness, not postulated. -/
theorem globalFiniteMaximalTrace_extra_injective
    (F K : ∀ {W : Type}, Structure L W → Prop)
    {V : Type}
    {Y : Structure (globalFunctionalPieceLanguage F) V}
    (hY : IsGlobalFiniteMaximalTrace F K Y)
    (s : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F s) → V)
    (h : Y.rel (.inr s) xs) :
    Function.Injective xs := by
  rcases hY with
    ⟨_, UW, W, _, _, iW, _, hRel⟩
  have hW :
      (globalFunctionalCanonicalLift F W).rel
        (.inr s) (iW ∘ xs) :=
    (hRel s xs).mp h
  have hinj :=
    globalFunctionalCanonicalRelation_injective F W
      s (iW ∘ xs) hW
  intro a b hab
  apply hinj
  exact congrArg iW hab

/-- Reassemble ANY global functional lift from its exact old shadow
and its complete family of added relations on the SAME carrier.
This is structural extensionality, not an assumption that a
canonical lift commutes with old-language restriction. -/
theorem globalFunctionalLift_reconstruct
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V : Type}
    (A : Structure L V)
    (Y : Structure (globalFunctionalPieceLanguage F) V)
    (hShadow : functionalShadowBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) Y = A) :
    Y = functionalWithExtraBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) A
      (fun s xs => Y.rel (.inr s) xs) := by
  let Z := functionalWithExtraBig L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F) A
    (fun s xs => Y.rel (.inr s) xs)
  have hR : Y.rel = Z.rel := by
    funext R xs
    cases R with
    | inl old =>
        change Y.rel (.inl old) xs = A.rel old.down xs
        exact congrArg
          (fun T : Structure L V => T.rel old.down xs) hShadow
    | inr tag =>
        rfl
  have hF : Y.func = Z.func := by
    funext f xs
    change Y.func f xs = A.func f.down xs
    exact congrArg
      (fun T : Structure L V => T.func f.down xs) hShadow
  change Y = Z
  cases Y with
  | mk relY funcY =>
      cases Z with
      | mk relZ funcZ =>
          cases hR
          cases hF
          rfl

/-- ALL actual maximal-trace age members over the literal old
shadow A, with equality of every original function fibre. -/
def GlobalMaximalTraceExactFibre
    (F K : ∀ {W : Type}, Structure L W → Prop)
    {V : Type} (A : Structure L V) :=
  {Y : Structure (globalFunctionalPieceLanguage F) V //
    functionalShadowBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) Y = A ∧
    IsGlobalFiniteMaximalTrace F K Y}

/-- Every genuine maximal trace in the EXACT fibre is one of the
named distinct-root lift options counted by regularity. -/
noncomputable def globalMaximalTraceExactFibre_toNamedOption
    (F K : ∀ {W : Type}, Structure L W → Prop)
    {V : Type} (A : Structure L V)
    (Y : GlobalMaximalTraceExactFibre F K A) :
    NamedGlobalLiftOptions F A := by
  classical
  let E : DistinctRootExtraData
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) V := {
    val := fun s xs => Y.1.rel (.inr s) xs
    property := by
      intro s xs h
      exact globalFiniteMaximalTrace_extra_injective
        F K Y.2.2 s xs h
  }
  refine ⟨Y.1, E, ?_⟩
  exact globalFunctionalLift_reconstruct F A Y.1 Y.2.1

/-- The encoding of actual maximal traces as named lift options
is INJECTIVE: no predicate information is discarded. -/
theorem globalMaximalTraceExactFibre_toNamedOption_injective
    (F K : ∀ {W : Type}, Structure L W → Prop)
    {V : Type} (A : Structure L V) :
    Function.Injective
      (globalMaximalTraceExactFibre_toNamedOption F K A) := by
  intro Y Z h
  apply Subtype.ext
  exact congrArg Subtype.val h

/-- Finiteness of the ENTIRE actual maximal-trace expansion fibre
over an arbitrary fixed finite original native structure. In
particular this is the precompactness statement for the original
regular root-injective lift, not just candidate-language counting. -/
theorem globalMaximalTraceExactFibre_finite
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    {V : Type} [Fintype V] (A : Structure L V) :
    Finite (GlobalMaximalTraceExactFibre F K A) := by
  letI : Finite (NamedGlobalLiftOptions F A) :=
    finite_namedGlobalLiftOptions_of_regular F A hRegular
  exact Finite.of_injective
    (globalMaximalTraceExactFibre_toNamedOption F K A)
    (globalMaximalTraceExactFibre_toNamedOption_injective F K A)

/-- Every finite K-allowed old shadow has a GENUINE member in
the EXACT maximal-trace fibre, by regular profile maximization.
This does not require K to have JEP or amalgamation. -/
theorem globalMaximalTraceExactFibre_nonempty
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    {V : Type} [Finite V]
    (A : Structure L V) (hA : K A) :
    Nonempty (GlobalMaximalTraceExactFibre F K A) := by
  obtain ⟨Y, hShadow, hAge⟩ :=
    globalFiniteMaximalTraceAge_exists_above
      F K hRegular A hA
  exact ⟨⟨Y, hShadow, hAge⟩⟩

/-- The exact genuine finite expansion fibre is nonempty IF AND
ONLY IF the old structure belongs to K, provided K is hereditary.
Combined with its verified finiteness, this certifies the full
precompact exact-reduct side of regular Section 3 homogenization. -/
theorem globalMaximalTraceExactFibre_nonempty_iff
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hHereditary : ∀ {UA UB : Type}
      {A : Structure L UA} {B : Structure L UB},
      Structure.Embedding A B → K B → K A)
    {V : Type} [Finite V] (A : Structure L V) :
    Nonempty (GlobalMaximalTraceExactFibre F K A) ↔ K A := by
  constructor
  · rintro ⟨⟨Y, hShadow, hAge⟩⟩
    exact (globalFiniteMaximalTraceAge_exact_reduct
      F K hRegular hHereditary A).mp
      ⟨Y, hShadow, hAge⟩
  · exact globalMaximalTraceExactFibre_nonempty
      F K hRegular A

end AllThoseRamseyClasses.Lifts
