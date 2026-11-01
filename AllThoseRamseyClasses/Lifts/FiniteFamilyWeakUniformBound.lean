import AllThoseRamseyClasses.Lifts.FiniteFamilyWeakLocalAvoidance
import Mathlib.Data.Fintype.Card

/-!
# Track E2: one explicit finite-family weak-test cutoff

For a FINITE named collection of finite forbidden native functional
sources, choose the maximum of their actual carrier cardinalities.
This bound depends only on the family, not on the Ramsey control,
a function-closure hull, or a chosen forbidden witness map.

If every EXACT weak induced subset S of a finite candidate D
of cardinality at most this cutoff has a finite forbidden-free
EHN completion, then D avoids the entire forbidden family.
The proof restricts any forbidden weak map to its actual image,
whose size is bounded by the cardinality of its finite source.
No injectivity of the forbidden map or function-closed image
is required, including when the native language has nullary
and arbitrarily high-arity set-valued function symbols.

This is an independently proved LOCAL-TO-GLOBAL inference.
It is NOT the missing partite sparsening theorem that builds
the weak-test completions while retaining the Ramsey arrow and
marked maximizing-witness copies.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Maximum cardinality of one of the genuinely named finite
forbidden sources. If the finite family is empty, the bound is 0. -/
noncomputable def finiteNamedMaxForbiddenSize
    (Family : FiniteNamedFunctionalSources.{u,0} L) : ℕ := by
  classical
  letI : Fintype Family.Index := Fintype.ofFinite Family.Index
  exact Finset.univ.sup (fun i : Family.Index =>
    Nat.card (Family.Carrier i))

/-- Every named forbidden source has at most the uniform cutoff
many vertices. The index type is allowed to be empty. -/
theorem finiteNamedSource_card_le_maxForbiddenSize
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (i : Family.Index) :
    Nat.card (Family.Carrier i) ≤
      finiteNamedMaxForbiddenSize Family := by
  classical
  letI : Fintype Family.Index := Fintype.ofFinite Family.Index
  unfold finiteNamedMaxForbiddenSize
  exact Finset.le_sup (Finset.mem_univ i)

/-- Exact-weak local completion condition with one EXPLICIT numeric
test cutoff depending only on the finite forbidden family. The
test S is a literal subset of the original finite candidate, not
a closure hull; the completion map may be noninjective and weak. -/
def FiniteNamedUniformWeakCompletions
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VD : Type} [Finite VD] (D : Structure L VD) : Prop :=
  ∀ (S : Set VD),
    Nat.card S ≤ finiteNamedMaxForbiddenSize Family →
    ∃ (VW : Type) (W : Structure L VW),
      Finite VW ∧ AvoidsFiniteNamedEHN Family W ∧
      ∃ (g : S → VW),
        (D.weakInduce S).IsEHNHomomorphismEmbedding W g

/-- The uniform-cardinality hypothesis supplies the source-specific
small-weak-image condition. The only cardinality argument is that
a surjection from the finite source carrier to S bounds the size
of S, even if many source vertices collide. -/
theorem FiniteNamedUniformWeakCompletions.to_sourceSmall
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VD : Type} [Finite VD] {D : Structure L VD}
    (h : FiniteNamedUniformWeakCompletions Family D) :
    FiniteNamedWeakSmallCompletions Family D := by
  intro i S hSurj
  obtain ⟨e, he⟩ := hSurj
  letI : Finite (Family.Carrier i) := Family.finiteCarrier i
  letI : Fintype (Family.Carrier i) := Fintype.ofFinite _
  letI : Finite S := inferInstance
  letI : Fintype S := Fintype.ofFinite _
  have hCard : Nat.card S ≤ Nat.card (Family.Carrier i) := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_surjective e he)
  exact h S (hCard.trans (finiteNamedSource_card_le_maxForbiddenSize Family i))

/-- All source-sized forbidden witnesses are excluded by weak
completions through one computable finite cutoff.

The result asserts NATIVE forbidden EHN avoidance, not the
existence of a Ramsey picture or preservation of any expanded
component-tag relations. -/
theorem avoidsFiniteNamedEHN_of_uniformWeakCompletions
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VD : Type} [Finite VD] (D : Structure L VD)
    (h : FiniteNamedUniformWeakCompletions Family D) :
    AvoidsFiniteNamedEHN Family D :=
  avoidsFiniteNamedEHN_of_weakSmallCompletions
    Family D (h.to_sourceSmall Family)

end AllThoseRamseyClasses.Lifts
