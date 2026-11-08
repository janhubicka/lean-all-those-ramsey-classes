import AllThoseRamseyClasses.Lifts.GlobalActualFairFraisseChain
import AllThoseRamseyClasses.Lifts.GlobalSurjectiveFullEmbeddingInverse

/-!
# Track F: genuine cofinality of the ENTIRE original finite maximal-trace age

The previously verified finite-age input provides actual
labelled full-isomorphism representatives on Fin n.
The fair finite chain visits each such representative
eventually, and indeed at every sufficiently late stage.

To show eventual cofinality of the WHOLE finite age, not just
the labelled representatives, we use the genuine surjective
FULL embedding P ↪ Y covering any finite age member Y.
The inverse full functional embedding Y ↪ P from the
independent theorem is composed with the fair chain's
FULL P-copy. This preserves every complete set-valued
function fibre, including nullaries and undefined fibres.

This proves an exact finite-cofinality prerequisite for the
future decoded native Fraïssé direct limit, without asserting
that the infinite limit or its native age equality is already
verified. The general root-injective shadow-avoidance
condition remains explicit in the finite-age input.

The numbered ramsey.tex is unchanged.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- EVERY finite original root-injective maximal-trace age
member Y, on any finite carrier, fully embeds into all
sufficiently late stages of the ACTUAL fair finite chain.
This is genuine age cofinality, not a statement only
about the countable labelled representatives. -/
theorem globalOriginalActualFairTraceChain_eventually_contains_age_member
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    {V : Type}
    (Y : Structure (globalFunctionalPieceLanguage F) V)
    (hY : IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (C : Structure L W) =>
        AvoidsGlobalFunctionalEHN F C) Y) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (_e : Structure.Embedding Y
        (globalOriginalActualFairTraceChain F hInput (n + 1)).model),
        True := by
  obtain ⟨P, e, heOnto⟩ :=
    hInput.coversEveryAgeMember Y hY
  obtain ⟨N, hN⟩ :=
    globalOriginalActualFairTraceChain_eventually_contains
      F hInput P
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨jP, _⟩ := hN n hn
  exact ⟨jP.comp (fullEmbeddingInverseOfSurjective e heOnto),
    True.intro⟩

end AllThoseRamseyClasses.Lifts
