import AllThoseRamseyClasses.Lifts.RegularLiftIsoTransport
import Mathlib.Data.Fintype.Basic

/-!
# Actual isomorphism-type precompactness of the regular canonical lift

Regularity of the 2019 global forbidden-piece setoid says that for each
positive root width, only finitely many global piece classes occur. The
distinct-root support theorem bounds ALL permitted extra relation tables
on one fixed finite carrier. The transport theorem then pulls back the
canonical lift of any isomorphic old-language structure along an old
FULL isomorphism.

This module assembles those separate verified constructions into a
literal finite list of expanded representatives. Every canonical
global functional lift of a shadow isomorphic to the fixed finite A
is FULLY isomorphic to one of the representatives on A's carrier.
This is the paper's *precompactness up to isomorphism* for canonical
distinct-root lifts of arbitrary regular families: no global bound on
root width, no finite-total-signature assumption, and no change to
original set-valued functional fibres.

It does NOT establish strong amalgamation, Ramsey, or the invalid
injectivization shortcut in the printed Section 3 proof. In
particular it does not apply to the collision-tolerant all-components
alternative, whose root tuples may have repeated coordinates.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u

/-- Under global regularity, one FINITE set of named representatives
on A's carrier covers the canonical functional lifts of ALL native
shadows fully isomorphic to A. The covering maps are full, surjective
embeddings of the entire expanded functional languages.

This is stronger than a mere cardinal upper bound on labelled extra
relation tables; it is the actual fixed-shadow isomorphism-type
precompactness statement for the original root-INJECTIVE lift. -/
theorem regularGlobalCanonicalLift_finiteIsoRepresentatives
    {L : Language.{u}}
    (F : ∀ {T : Type}, Structure L T → Prop)
    {V : Type} [Fintype V]
    (A : Structure L V)
    (hRegular : GlobalFunctionalPieceRegular F) :
    ∃ (reps : Finset (NamedGlobalLiftOptions F A)),
      ∀ {W : Type} (B : Structure L W)
        (e : Structure.Embedding A B)
        (he : Function.Surjective e),
        ∃ (P : NamedGlobalLiftOptions F A), P ∈ reps ∧
          ∃ (g : Structure.Embedding P.1
            (globalFunctionalCanonicalLift F B)),
            Function.Surjective g := by
  classical
  letI : Finite (NamedGlobalLiftOptions F A) :=
    finite_namedGlobalLiftOptions_of_regular F A hRegular
  letI : Fintype (NamedGlobalLiftOptions F A) :=
    Fintype.ofFinite _
  refine ⟨Finset.univ, ?_⟩
  intro W B e he
  let hShadow := globalFunctionalCanonicalLift_shadow F B
  have hDistinct :
      ∀ (i : GlobalFunctionalPieceSymbol F)
        (xs : Fin (globalFunctionalPieceArity F i) → W),
        (globalFunctionalCanonicalLift F B).rel (.inr i) xs →
        Function.Injective xs := by
    intro i xs h
    exact globalFunctionalCanonicalRelation_injective F B i xs h
  let P : NamedGlobalLiftOptions F A :=
    pullbackGlobalLiftOption F A B
      (globalFunctionalCanonicalLift F B)
      hShadow e hDistinct
  refine ⟨P, Finset.mem_univ P, ?_⟩
  refine ⟨pullbackGlobalLiftEmbedding F A B
      (globalFunctionalCanonicalLift F B)
      hShadow e hDistinct, ?_⟩
  exact pullbackGlobalLiftEmbedding_surjective F A B
    (globalFunctionalCanonicalLift F B)
    hShadow e hDistinct he

end AllThoseRamseyClasses.Lifts
