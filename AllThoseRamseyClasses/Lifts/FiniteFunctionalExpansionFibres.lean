import AllThoseRamseyClasses.Lifts.FunctionalLiftLanguageBig
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets

/-!
# Finite choices of added relations over one finite functional shadow

The canonical Section 3 lift, and any proposed folded-root
alternative, add ONLY relation symbols and leave the old relation
and function interpretations literally unchanged.

For a FIXED finite carrier and a FINITE set of new relation symbols
of finite arities, there are only finitely many distinct expansions
of one given original functional structure.

This is a general finite-signature precompactness lemma. It does
NOT prove the crucial additional hypothesis that a regular infinite
forbidden-piece family has only finitely many positive-width global
symbols; regularity gives finite fibres at each arity, not a
uniform bound on arities. Nor does it prove finite-family class
amalgamation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w

/-- The exact fibre of the shadow functor on ONE fixed carrier and
ONE given old relation/function structure. Old function domains,
entire value sets, and old relation tuples cannot vary. -/
def FixedFunctionalShadowExpansions
    (L : Language.{u})
    (New : Type w) (ar : New → ℕ)
    {V : Type v} (A : Structure L V) :=
  {Y : Structure (functionalLiftLanguageBig L New ar) V //
    functionalShadowBig L New ar Y = A}

/-- For finite old carriers and finitely many new symbols, the
extra relation interpretations determine any expansion with a
fixed full functional shadow uniquely. Thus its expansion fibre
is finite, regardless of the number of OLD relation/function symbols. -/
theorem fixedFunctionalShadowExpansions_finite
    (L : Language.{u})
    (New : Type w) (ar : New → ℕ)
    {V : Type v} [Finite V] [Finite New]
    (A : Structure L V) :
    Finite (FixedFunctionalShadowExpansions L New ar A) := by
  classical
  have hFiniteData :
      Finite (∀ i : New, (Fin (ar i) → V) → Prop) := inferInstance
  apply Finite.of_injective
    (fun Y : FixedFunctionalShadowExpansions L New ar A =>
      fun (i : New) (xs : Fin (ar i) → V) =>
        Y.1.rel (.inr i) xs)
  intro Y Z hNew
  have hShadow :
      functionalShadowBig L New ar Y.1 =
        functionalShadowBig L New ar Z.1 :=
    Y.2.trans Z.2.symm
  have hOldRel (R : L.RelSymbol) :
      Y.1.rel (.inl (ULift.up R)) =
        Z.1.rel (.inl (ULift.up R)) :=
    congrArg (fun S : Structure L V => S.rel R) hShadow
  have hOldFunc (F : L.FuncSymbol) :
      Y.1.func (ULift.up F) =
        Z.1.func (ULift.up F) :=
    congrArg (fun S : Structure L V => S.func F) hShadow
  have hAllRel : Y.1.rel = Z.1.rel := by
    funext s
    cases s with
    | inl R =>
        cases R with
        | up R => exact hOldRel R
    | inr i =>
        exact congrFun hNew i
  have hAllFunc : Y.1.func = Z.1.func := by
    funext F
    cases F with
    | up G => exact hOldFunc G
  cases Y with
  | mk Y hY =>
    cases Z with
    | mk Z hZ =>
      apply Subtype.ext
      cases Y with
      | mk relY funcY =>
        cases Z with
        | mk relZ funcZ =>
          dsimp at hAllRel hAllFunc
          cases hAllRel
          cases hAllFunc
          rfl

end AllThoseRamseyClasses.Lifts
