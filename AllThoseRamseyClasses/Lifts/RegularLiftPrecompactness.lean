import AllThoseRamseyClasses.Lifts.FiniteRootTupleLiftData
import AllThoseRamseyClasses.Lifts.GlobalFunctionalPieceLift

/-!
# Regular forbidden-piece families have finite labelled functional lifts

The relation expansion of Section 3 uses one symbol for each GLOBAL
incompatibility class of a genuine forbidden piece of positive root
width. Regularity means that the quotient class type at each such
width is finite, NOT that the whole infinite lift language is finite.

On a finite carrier V, any relation tuple with distinct coordinates
has arity at most card V. We therefore collect the finitely many
global class symbols of widths between 1 and card V into one FINITE
active index. Every canonical extra relation is determined by its
truth values on this finite family of symbols and their tuples.

The theorem proves finite labelled relation-lift data. This is
stronger than the numerical bound on isomorphism types required for
the paper's precompactness definition, but does not yet assert
finite number of entire expansions of a changed underlying carrier.
Old function interpretations never vary: the functional shadow is
exactly the fixed old structure.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u

/-- Regularity is finiteness of actual selected forbidden-piece
equivalence classes at EVERY positive root width. No global
bound on root width or number of piece classes is assumed. -/
def GlobalFunctionalPieceRegular
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop) : Prop :=
  ∀ n : ℕ, 0 < n → Finite (GlobalFunctionalPieceClass F n)

/-- Under regularity, all labelled extra-relation interpretations
supported on injective tuples form a FINITE type on each finite
vertex carrier, even for an infinite lift signature. -/
theorem finite_globalDistinctRootExtraData_of_regular
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    (V : Type) [Fintype V]
    (hRegular : GlobalFunctionalPieceRegular F) :
    Finite
      (DistinctRootExtraData
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) V) := by
  classical
  let m : ℕ := Fintype.card V
  let Active :=
    Σ k : {j : Fin (m + 1) // 0 < j.1},
      GlobalFunctionalPieceClass F k.1.1
  letI (k : {j : Fin (m + 1) // 0 < j.1}) :
      Finite (GlobalFunctionalPieceClass F k.1.1) :=
    hRegular k.1.1 k.2
  haveI : Finite Active := inferInstance
  let index : Active → GlobalFunctionalPieceSymbol F :=
    fun s => ⟨⟨s.1.1.1, s.1.2⟩, s.2⟩
  apply finite_distinctRootExtraData_of_active index
  intro i xs hinj
  have hle : globalFunctionalPieceArity F i ≤ m :=
    Fintype.card_le_of_injective xs hinj
  let k : {j : Fin (m + 1) // 0 < j.1} :=
    ⟨⟨globalFunctionalPieceArity F i,
        Nat.lt_succ_of_le hle⟩,
      globalFunctionalPieceArity_positive F i⟩
  exact ⟨⟨k, i.2⟩, rfl⟩

/-- The actual canonical lift's new relation interpretations are
members of the finite labelled candidate type. This uses no
assumption about hereditary/amalgamation properties of F. -/
def globalCanonicalDistinctRootExtraData
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V : Type} (A : Structure L V) :
    DistinctRootExtraData
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) V :=
  canonicalExtraData
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F)
    (globalFunctionalPieceRepresentatives F) A

/-- The canonical interpretation is one of FINITELY many possible
labelled root-injective expansions of A, uniformly over any
finite original structure A in the fixed vertex carrier V. -/
theorem finite_globalCanonicalLiftOptions_of_regular
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    (V : Type) [Fintype V]
    (hRegular : GlobalFunctionalPieceRegular F) :
    Finite
      (DistinctRootExtraData
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) V) :=
  finite_globalDistinctRootExtraData_of_regular F V hRegular

end AllThoseRamseyClasses.Lifts
