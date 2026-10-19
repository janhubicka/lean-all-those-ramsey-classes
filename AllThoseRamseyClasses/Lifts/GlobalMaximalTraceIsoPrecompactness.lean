import AllThoseRamseyClasses.Lifts.GlobalMaximalTraceExactFibre
import AllThoseRamseyClasses.Lifts.RegularLiftIsoTransport

/-!
# Precompactness up to isomorphism for the ACTUAL global maximal-trace age

The previous exact-fibre theorem counts all actual maximal induced
global canonical traces with one FIXED finite original functional
shadow A. The paper's precompactness claim concerns all expansions
of shadows ISOMORPHIC to A, possibly on other finite carriers.

A full old-language isomorphism e : A ≃ shadow(Y) pulls the entire
new relation interpretation of any genuine maximal-trace Y back
to A. Maximal-trace relations have distinct roots, by their actual
induced canonical-witness semantics. The previously verified
pullback is a FULL expanded embedding, and maximal-trace membership
is hereditary under that embedding. When e is surjective, the new
expanded embedding is onto as well.

Hence each finite original A has finitely many ACTUAL maximal-trace
expanded representatives covering all isomorphic finite shadows.
This is stronger than finiteness of arbitrary candidate relation
tables or canonical lifts alone.

No Ramsey, strong amalgamation, JEP or unproved forbidden-family
shadow-avoidance assumption enters the proof. The original entire
functional fibres are unchanged, including nullary inputs.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Any genuine finite global maximal-trace age member over a shadow
fully isomorphic to A can be pulled back to an actual maximal-trace
age member with EXACT native shadow A. The map is a surjective FULL
embedding of entire expanded functional structures.

This transport itself does not require regularity: it uses only the
distinct-root semantics and hereditary membership of maximal traces.
-/
theorem globalMaximalTraceAge_pullback_iso
    (F K : ∀ {W : Type}, Structure L W → Prop)
    {VA VW : Type}
    (A : Structure L VA)
    (Y : Structure (globalFunctionalPieceLanguage F) VW)
    (hY : IsGlobalFiniteMaximalTrace F K Y)
    (e : Structure.Embedding A
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) Y))
    (he : Function.Surjective e) :
    ∃ (P : GlobalMaximalTraceExactFibre F K A),
      ∃ (j : Structure.Embedding P.1 Y),
        Function.Surjective j := by
  classical
  let B : Structure L VW :=
    functionalShadowBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) Y
  have hDistinct :
      ∀ (s : GlobalFunctionalPieceSymbol F)
        (xs : Fin (globalFunctionalPieceArity F s) → VW),
        Y.rel (.inr s) xs → Function.Injective xs := by
    intro s xs h
    exact globalFiniteMaximalTrace_extra_injective F K hY s xs h
  let P : NamedGlobalLiftOptions F A :=
    pullbackGlobalLiftOption F A B Y rfl e hDistinct
  let j : Structure.Embedding P.1 Y :=
    pullbackGlobalLiftEmbedding F A B Y rfl e hDistinct
  have hPAge : IsGlobalFiniteMaximalTrace F K P.1 :=
    IsGlobalFiniteMaximalTrace.of_embedding F K hY j
  have hj : Function.Surjective j :=
    pullbackGlobalLiftEmbedding_surjective F A B Y
      rfl e hDistinct he
  exact ⟨⟨P.1, namedGlobalLiftOptions_shadow F A P, hPAge⟩,
    j, hj⟩

/-- The ACTUAL regular maximal-trace age is precompact up to
isomorphism: for each fixed finite old structure A, there is one
finite set of actual full maximal-trace expansions over the same
carrier covering EVERY maximal-trace age member whose old shadow
is fully isomorphic to A.

No global bound on the new language's arities and no globally
finite set of relation symbols is assumed. -/
theorem globalMaximalTraceAge_finiteIsoRepresentatives
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    {VA : Type} [Fintype VA]
    (A : Structure L VA) :
    ∃ (reps : Finset (GlobalMaximalTraceExactFibre F K A)),
      ∀ {VW : Type}
        (Y : Structure (globalFunctionalPieceLanguage F) VW)
        (hY : IsGlobalFiniteMaximalTrace F K Y)
        (e : Structure.Embedding A
          (functionalShadowBig L
            (GlobalFunctionalPieceSymbol F)
            (globalFunctionalPieceArity F) Y))
        (he : Function.Surjective e),
        ∃ (P : GlobalMaximalTraceExactFibre F K A),
          P ∈ reps ∧
          ∃ (j : Structure.Embedding P.1 Y),
            Function.Surjective j := by
  classical
  letI : Finite (GlobalMaximalTraceExactFibre F K A) :=
    globalMaximalTraceExactFibre_finite F K hRegular A
  letI : Fintype (GlobalMaximalTraceExactFibre F K A) :=
    Fintype.ofFinite _
  refine ⟨Finset.univ, ?_⟩
  intro VW Y hY e he
  obtain ⟨P, j, hj⟩ :=
    globalMaximalTraceAge_pullback_iso F K A Y hY e he
  exact ⟨P, Finset.mem_univ P, j, hj⟩

end AllThoseRamseyClasses.Lifts
