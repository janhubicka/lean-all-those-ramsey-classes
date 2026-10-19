import AllThoseRamseyClasses.Lifts.FunctionalBigExpansionPullback
import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTracePrecompactness

/-!
# Isomorphism-type precompactness of the finite-family maximal-trace age

The finite-family folded all-closed-component age has genuine nonempty
finite expansion fibres over each fixed finite forbidden-free original
shadow. Its relations allow COLLIDING root images, so the printed
distinct-root transport cannot be used.

Instead use the generic relation-only functional pullback: a FULL
old shadow isomorphism A ≃ shadow(Y) transports every added folded
relation to A while preserving entire old function fibres.
Heredity of the actual maximal induced-trace age shows that this
pulled-back expansion belongs to the age; the underlying map is
a FULL expanded isomorphism onto Y.

Thus the finite-family alternative is genuinely precompact UP TO
ISOMORPHISM of old native functional shadows, not merely finite
candidate relation tables. This statement does not establish Ramsey
or the printed infinite-regular-family strong-amalgamation theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Each actual folded maximal-trace age member whose full old shadow
is isomorphic to A has a FULLY isomorphic age representative with
EXACT native shadow A. This handles repeated root coordinates. -/
theorem finiteNamedMaximalTraceAge_pullback_iso
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VA VW : Type}
    (A : Structure L VA)
    (Y : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VW)
    (hY : IsFiniteNamedMaximalTrace Family Y)
    (e : Structure.Embedding A (FiniteNamedTraceShadow Family Y))
    (he : Function.Surjective e) :
    ∃ (P : FiniteNamedMaximalTraceFibre Family A),
      ∃ (j : Structure.Embedding P.1.1 Y),
        Function.Surjective j := by
  let X := functionalBigExpansionPullback
    L Family.ComponentTag (fun tag => tag.width Family) A Y e
  let j : Structure.Embedding X Y :=
    functionalBigExpansionPullbackEmbedding
      L Family.ComponentTag (fun tag => tag.width Family) A Y e
  have hX : IsFiniteNamedMaximalTrace Family X :=
    IsFiniteNamedMaximalTrace.of_embedding Family hY j
  have hShadow : FiniteNamedTraceShadow Family X = A :=
    functionalBigExpansionPullback_shadow
      L Family.ComponentTag (fun tag => tag.width Family) A Y e
  have hj : Function.Surjective j :=
    functionalBigExpansionPullbackEmbedding_surjective
      L Family.ComponentTag (fun tag => tag.width Family) A Y e he
  exact ⟨⟨⟨X, hShadow⟩, hX⟩, j, hj⟩

/-- A finite family of finite native EHN forbidden sources admits one
FINITE set of ACTUAL maximal folded expansions over any finite A,
covering by full expanded isomorphism every age member whose
original native shadow is fully isomorphic to A.

No global canonical relation root-injectivity is assumed; this
is precompactness of the full alternative lifted age. -/
theorem finiteNamedMaximalTraceAge_finiteIsoRepresentatives
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VA : Type} [Finite VA]
    (A : Structure L VA) :
    ∃ (reps : Finset (FiniteNamedMaximalTraceFibre Family A)),
      ∀ {VW : Type}
        (Y : Structure
          (functionalLiftLanguageBig L Family.ComponentTag
            (fun tag => tag.width Family)) VW)
        (hY : IsFiniteNamedMaximalTrace Family Y)
        (e : Structure.Embedding A (FiniteNamedTraceShadow Family Y))
        (he : Function.Surjective e),
        ∃ (P : FiniteNamedMaximalTraceFibre Family A),
          P ∈ reps ∧
          ∃ (j : Structure.Embedding P.1.1 Y),
            Function.Surjective j := by
  classical
  letI : Finite (FiniteNamedMaximalTraceFibre Family A) :=
    finiteNamedMaximalTraceFibre_finite Family A
  letI : Fintype (FiniteNamedMaximalTraceFibre Family A) :=
    Fintype.ofFinite _
  refine ⟨Finset.univ, ?_⟩
  intro VW Y hY e he
  obtain ⟨P, j, hj⟩ :=
    finiteNamedMaximalTraceAge_pullback_iso Family A Y hY e he
  exact ⟨P, Finset.mem_univ P, j, hj⟩

end AllThoseRamseyClasses.Lifts
