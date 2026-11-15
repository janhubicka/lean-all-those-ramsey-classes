import AllThoseRamseyClasses.Lifts.GlobalPieceFixedRootBridge
import Mathlib.Data.Fintype.EquivFin

/-!
# Width-one threshold obstruction for the genuine global piece quotient

This theorem isolates the FINITENESS failure created when actual
selected width-one forbidden pieces P_i have test profiles
  Incompatible(P_i,Q_j) iff j <= i.

A rooted test Q_j can be ANY full functional root chart. We do not
replace the true global canonical Myhill--Nerode quotient by a
surrogate equality relation or a finite table.

The accompanying mathematical note constructs connected coloured
graphs F_i, a regular infinite family F, and rooted pieces of
its full-range EHN saturation exhibiting this threshold. The
concrete graph-to-native Lean bridge is still pending; only this
abstract threshold-to-infinite-classes implication is claimed here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A genuine threshold of selected width-one piece incompatibility
profiles produces INFINITELY MANY distinct global quotient symbols.
The test charts are unrestricted: they need not themselves be
selected forbidden pieces. -/
theorem infiniteGlobalPieceClasses_of_orderThreshold
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : ℕ → SelectedFunctionalChart F 1)
    (Q : ℕ → FunctionalRootChart L 1)
    (hThreshold : ∀ i j : ℕ,
      FunctionalRootChart.Incompatible F (P i).1 (Q j) ↔ j ≤ i) :
    Infinite (GlobalFunctionalPieceClass F 1) := by
  let label : ℕ → GlobalFunctionalPieceClass F 1 :=
    fun i => Quotient.mk (globalFunctionalPieceSetoid F 1) (P i)
  have hInjective : Function.Injective label := by
    intro i j hEq
    have hEquivalent :
        (globalFunctionalPieceSetoid F 1).r (P i) (P j) :=
      Quotient.exact hEq
    rcases lt_trichotomy i j with hij | hij | hji
    · have hJ :
          FunctionalRootChart.Incompatible F (P j).1 (Q j) :=
        (hThreshold j j).mpr (le_refl j)
      have hI :
          FunctionalRootChart.Incompatible F (P i).1 (Q j) :=
        (incompatible_iff_of_equiv hEquivalent (Q j)).mpr hJ
      have hLe : j ≤ i := (hThreshold i j).mp hI
      exact False.elim ((not_le.mpr hij) hLe)
    · exact hij
    · have hI :
          FunctionalRootChart.Incompatible F (P i).1 (Q i) :=
        (hThreshold i i).mpr (le_refl i)
      have hJ :
          FunctionalRootChart.Incompatible F (P j).1 (Q i) :=
        (incompatible_iff_of_equiv hEquivalent (Q i)).mp hI
      have hLe : i ≤ j := (hThreshold j i).mp hJ
      exact False.elim ((not_le.mpr hji) hLe)
  exact Infinite.of_injective label hInjective

end AllThoseRamseyClasses.Lifts
