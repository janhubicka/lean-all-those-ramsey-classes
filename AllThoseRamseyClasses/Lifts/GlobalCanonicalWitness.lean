import AllThoseRamseyClasses.Lifts.ForbiddenPieceProfileNonempty

/-!
# Canonical relation witness extraction for the GLOBAL piece quotient

The 2019 Section 3 lift has a relation for each equivalence class of
genuinely selected forbidden pieces. Every positive-width class
symbol is the quotient of ALL selected pieces by their incompatibility
profiles against arbitrary compatible rooted tests.

Its extra relation has an exact existential interpretation:
a DISTINCT root tuple has a weak rooted realization by some selected
piece in the class. Because every selected piece has an actual
forbidden complementary test, equal global classes now force equality
of the COMPLETE induced functional root structure.

Consequently a global canonical relation supplies not only a weakly
realized replacement piece, but one with precisely the original
functional root (up to the equality supplied by the quotient).
No guessed representative, root-cardinality-only matching or
injectivity of a general weak map is assumed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- The global new relation symbol represented by a genuinely
selected forbidden piece of positive root width. -/
def globalPieceSymbolOf
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : SelectedFunctionalChart F n)
    (hn : 0 < n) : GlobalFunctionalPieceSymbol F :=
  ⟨⟨n, hn⟩, Quotient.mk (globalFunctionalPieceSetoid F n) P⟩

@[simp] theorem globalPieceSymbolOf_arity
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : SelectedFunctionalChart F n)
    (hn : 0 < n) :
    globalFunctionalPieceArity F (globalPieceSymbolOf F P hn) = n := rfl

/-- An occurrence of the global class relation is exactly a
distinct ordered tuple and a weak realization by an ACTUAL
selected piece whose global incompatibility class equals P's. -/
theorem globalCanonicalRelation_of_symbol_iff
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : SelectedFunctionalChart F n)
    (hn : 0 < n)
    {W : Type} (A : Structure L W)
    (xs : Fin n → W) :
    (globalFunctionalCanonicalLift F A).rel
        (.inr (globalPieceSymbolOf F P hn)) xs ↔
      Function.Injective xs ∧
        ∃ Q : SelectedFunctionalChart F n,
          Quotient.mk (globalFunctionalPieceSetoid F n) Q =
            Quotient.mk (globalFunctionalPieceSetoid F n) P ∧
          FunctionalRootRealization Q.1.pattern A xs := by
  exact globalFunctionalCanonicalRelation_iff F A
    (globalPieceSymbolOf F P hn) xs

/-- Every global piece-class witness has the SAME complete functional
root as the selected representative. The proof is not a mere
cardinality argument: it uses the nonempty forbidden complement
constructed from a genuine finite forbidden source. -/
theorem globalCanonicalRelation_compatible_witness
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : SelectedFunctionalChart F n)
    (hn : 0 < n)
    {W : Type} (A : Structure L W)
    (xs : Fin n → W)
    (h : (globalFunctionalCanonicalLift F A).rel
        (.inr (globalPieceSymbolOf F P hn)) xs) :
    Function.Injective xs ∧
      ∃ Q : SelectedFunctionalChart F n,
        P.1.root = Q.1.root ∧
        (globalFunctionalPieceSetoid F n).r P Q ∧
        FunctionalRootRealization Q.1.pattern A xs := by
  obtain ⟨hinj, Q, hquot, hreal⟩ :=
    (globalCanonicalRelation_of_symbol_iff F P hn A xs).mp h
  have hQP : (globalFunctionalPieceSetoid F n).r Q P :=
    Quotient.exact hquot
  have hPQ : (globalFunctionalPieceSetoid F n).r P Q :=
    (globalFunctionalPieceSetoid F n).iseqv.symm hQP
  have hroot : P.1.root = Q.1.root :=
    globalFunctionalPiece_equiv_root_eq F P Q hPQ
  exact ⟨hinj, Q, hroot, hPQ, hreal⟩

/-- A weak realization of an actual selected representative
introduces its global canonical class relation provided the
ordered root-image tuple is INJECTIVE, as required by the printed
definition of the canonical lift. -/
theorem globalCanonicalRelation_of_selected_weak
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : SelectedFunctionalChart F n)
    (hn : 0 < n)
    {W : Type} (A : Structure L W)
    (f : P.1.ext.Carrier → W)
    (hf : P.1.ext.str.IsEHNHomomorphismEmbedding A f)
    (hinj : Function.Injective
      (fun i : Fin n => f (P.1.ext.rootEmbedding i))) :
    (globalFunctionalCanonicalLift F A).rel
      (.inr (globalPieceSymbolOf F P hn))
      (fun i : Fin n => f (P.1.ext.rootEmbedding i)) := by
  apply (globalCanonicalRelation_of_symbol_iff F P hn A
    (fun i : Fin n => f (P.1.ext.rootEmbedding i))).mpr
  refine ⟨hinj, P, rfl, ?_⟩
  exact ⟨f, hf, fun _ => rfl⟩

/-- If the global class relation realized in the first witness
occurs on the corresponding roots in the second witness, the
second witness contains a weak realization by an ACTUAL selected
piece with the same entire functional root as the first.

Only one globally indexed class relation is needed. This is the
global canonical-lift witness step of the published flip argument,
still conditional on having matching root tuples and an injective
root image in the first weak realization. -/
theorem globalCanonicalWitness_from_shared_relation
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : SelectedFunctionalChart F n)
    (hn : 0 < n)
    {W Z : Type}
    (A : Structure L W) (B : Structure L Z)
    (f : P.1.ext.Carrier → W)
    (hf : P.1.ext.str.IsEHNHomomorphismEmbedding A f)
    (hinj : Function.Injective
      (fun i : Fin n => f (P.1.ext.rootEmbedding i)))
    (xsB : Fin n → Z)
    (hShared :
      (globalFunctionalCanonicalLift F A).rel
        (.inr (globalPieceSymbolOf F P hn))
        (fun i : Fin n => f (P.1.ext.rootEmbedding i)) →
      (globalFunctionalCanonicalLift F B).rel
        (.inr (globalPieceSymbolOf F P hn)) xsB) :
    Function.Injective xsB ∧
      ∃ Q : SelectedFunctionalChart F n,
        P.1.root = Q.1.root ∧
        (globalFunctionalPieceSetoid F n).r P Q ∧
        ∃ g : Q.1.ext.Carrier → Z,
          Q.1.ext.str.IsEHNHomomorphismEmbedding B g ∧
          ∀ i : Fin n, g (Q.1.ext.rootEmbedding i) = xsB i := by
  have hRelA := globalCanonicalRelation_of_selected_weak
    F P hn A f hf hinj
  obtain ⟨hInj, Q, hRoot, hEq, ⟨g, hg, hcoords⟩⟩ :=
    globalCanonicalRelation_compatible_witness F P hn B xsB
      (hShared hRelA)
  exact ⟨hInj, Q, hRoot, hEq, g, hg, hcoords⟩

end AllThoseRamseyClasses.Lifts
