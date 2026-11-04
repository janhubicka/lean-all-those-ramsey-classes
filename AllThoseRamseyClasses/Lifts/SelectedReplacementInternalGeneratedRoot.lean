import AllThoseRamseyClasses.Lifts.GeometricSelectedInternalBoundary
import AllThoseRamseyClasses.Lifts.FunctionalRootedIsoInternalBoundaryInvariant
import AllThoseRamseyClasses.Lifts.SelectedGlobalFlipGeometricWitness

/-!
# A canonical selected replacement Q is a genuine inner geometric component

The original 2019 canonical global piece relation supplies an
ACTUAL selected forbidden geometric source piece Q up to a full
root-preserving isomorphism; the strengthened literal source flip
(#766) retains precisely this Q and its source certificate.

The source-geometric internal boundary theorem (#799) proves
that every selected forbidden geometric pattern has ONE genuinely
connected component outside its complete ordered root whose
entire native function-generated external boundary equals that
root. Exact rooted-isomorphism transport (#801) carries this
equation to the same selected Q.

This establishes Q's private geometric component and boundary
without inferring connectivity from a generic arbitrary root
extension or assuming the desired boundary equation. The
next step can insert that component into the literal source flip
via #782 and recover a genuine outer geometry via #786.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- The genuine selected replacement source piece Q represented by
the original global lift has an ACTUAL connected private component
whose complete generated boundary is precisely its full ordered
root, not merely a subset or direct-neighbour boundary.

No root-image injectivity of the weak forbidden map is assumed:
the isomorphism is an ONTO FULL native source-root isomorphism. -/
theorem selectedReplacementPiece_has_internalGeneratedRoot
    (F : ∀ {W : Type}, Structure L W → Prop)
    (R : Structure L (Fin n))
    (Q : FunctionalRootExtension R)
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        R (Equiv.refl (Fin n)) Q) ∈
          forbiddenGeometricFunctionalPieces F n) :
    ∃ x : {a : Q.Carrier // a ∉ Set.range Q.rootEmbedding},
      Q.str.functionClosure
        (gaifmanNeighborhood Q.str.graph
          (componentFrom Q.str.graph
            (Set.range Q.rootEmbedding) x)) =
      Set.range Q.rootEmbedding := by
  change IsForbiddenGeometricFunctionalPiece F
    (FunctionalRootExtension.toEnumeratedRootedPattern
      R (Equiv.refl (Fin n)) Q) at hSelected
  obtain ⟨W, A, _hFinite, _hFA, d, ⟨e⟩⟩ := hSelected
  have hGeometric :
      ∃ x :
        {a : (geometricFunctionalRootedPattern A d).Carrier //
          a ∉ Set.range (geometricFunctionalRootedPattern A d).root},
        (geometricFunctionalRootedPattern A d).str.functionClosure
          (gaifmanNeighborhood
            (geometricFunctionalRootedPattern A d).str.graph
            (componentFrom
              (geometricFunctionalRootedPattern A d).str.graph
              (Set.range (geometricFunctionalRootedPattern A d).root)
              x)) =
          Set.range (geometricFunctionalRootedPattern A d).root := by
    exact geometricGlobalSelectedPiece_internalBoundary_eq_root A d
  have hQPattern :=
    functionalRootedIso_internalBoundary_forward e.symm hGeometric
  exact hQPattern

end AllThoseRamseyClasses.Lifts
