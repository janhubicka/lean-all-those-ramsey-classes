import AllThoseRamseyClasses.Lifts.ForbiddenGeometricFunctionalPieces
import AllThoseRamseyClasses.Lifts.GeometricGlobalPieceSymbol
import Mathlib.Data.Fintype.Card

/-!
# Track B: a uniform forbidden-source size bound controls every selected Q

The global functional piece family consists of actual rooted
FULL-induced pieces of genuine finite F-forbidden source
structures, up to FULL root-preserving isomorphism. An isomorphism
of relationalized rooted graph patterns is a bijection on the
literal SOURCE carriers, not a weak target-image quotient.

If the forbidden family F has a UNIFORM finite SOURCE size
bound N, every selected width-m forbidden rooted pattern has
at most N SOURCE vertices. Consequently the literal Q carried
by any same-selected-Q native free-amalgam step has size at most N.

This is a CONDITIONAL theorem: the original 2019 Claim 2
does not automatically require a uniformly bounded F, and
finiteness of each F member ALONE does not supply a common
numerical N. Nor does an N bound ensure that all positive
B-rank states have a selected-Q successor rather than
old-root-capture/A-mixedness.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every actual selected rooted forbidden functional pattern
embeds by its ROOT-PRESERVING FULL pattern isomorphism into
the original finite forbidden source that generated it.

Thus a uniform upper bound on the SOURCE size of every F-member
also bounds the genuine rooted-pattern carrier cardinality,
independent of target-map collisions, ordering and root width. -/
theorem forbiddenGeometricFunctionalPiece_finite_card_le_uniformBound
    (F : ∀ {W : Type}, Structure L W → Prop)
    (bound : ℕ)
    (hUniform : ∀ {W : Type} (A : Structure L W),
      F A → Nat.card W ≤ bound)
    {m : ℕ}
    (P : FunctionalRootedPattern.{u,0} L m)
    (hSelected : P ∈ forbiddenGeometricFunctionalPieces F m) :
    Finite P.Carrier ∧ Nat.card P.Carrier ≤ bound := by
  classical
  obtain ⟨W, Source, hFinite, hForbidden, d, ⟨e⟩⟩ :=
    forbiddenGeometricFunctionalPieces_has_source F P hSelected
  letI : Finite W := hFinite
  let embed : P.Carrier → W :=
    fun p => (e.equiv p).1
  have hInj : Function.Injective embed := by
    intro x y h
    apply e.equiv.injective
    exact Subtype.ext h
  haveI : Finite P.Carrier := Finite.of_injective embed hInj
  letI : Fintype W := Fintype.ofFinite W
  letI : Fintype P.Carrier := Fintype.ofFinite P.Carrier
  have hCard :
      Nat.card P.Carrier ≤ Nat.card W := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_injective embed hInj)
  exact ⟨inferInstance, hCard.trans (hUniform Source hForbidden)⟩

/-- In particular, the SAME selected forbidden functional
root extension Q inserted by a native selected-Q construction
has at most bound literal Q SOURCE vertices. The result includes
a genuine Finite Q.Carrier certificate, not just the potentially
misleading Nat.card of an infinite carrier. -/
theorem selectedForbiddenQ_finite_card_le_uniformBound
    (F : ∀ {W : Type}, Structure L W → Prop)
    (bound : ℕ)
    (hUniform : ∀ {W : Type} (A : Structure L W),
      F A → Nat.card W ≤ bound)
    {m : ℕ}
    (Root : Structure L (Fin m))
    (Q : FunctionalRootExtension Root)
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern Root
        (Equiv.refl (Fin m)) Q) ∈
        forbiddenGeometricFunctionalPieces F m) :
    Finite Q.Carrier ∧ Nat.card Q.Carrier ≤ bound := by
  exact forbiddenGeometricFunctionalPiece_finite_card_le_uniformBound
    F bound hUniform
    (FunctionalRootExtension.toEnumeratedRootedPattern Root
      (Equiv.refl (Fin m)) Q) hSelected

end AllThoseRamseyClasses.Lifts
