import AllThoseRamseyClasses.Lifts.MinimalSeparatorForward
import Mathlib.Data.Set.Card

/-!
# Choosing inclusion-minimal closed separating cuts in finite structures

Proposition `prop:sep` of the 2019 manuscript uses genuine
inclusion-minimal separating cuts, not merely an arbitrary closed
separator. The existing boundary-closure characterization presupposes
such a minimal cut. Here we construct one INSIDE any supplied closed
separating cut when the source carrier is finite.

Choose a separating closed subset of least finite cardinality.
Any proper closed subset that still separates the same two vertices
would be another candidate of strictly smaller cardinality.

The proof is entirely about the actual native function-closed sets.
The two distinguished vertices are transported to smaller cuts with
`outsideCutMap`; no closure hull or weak-map injectivity assumption
is introduced. Finiteness is essential for this selection step.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Every closed separator of two vertices in a finite native
functional structure contains a minimal CLOSED separator for the
same two vertices. The new cut is contained in the original one. -/
theorem finite_exists_minimalClosedSeparator_inside
    [Finite V]
    (A : Structure L V) (S : Set V)
    (hSclosed : A.IsClosed S)
    (x y : {z : V // z ∉ S})
    (hSep : ¬ ReachOutside A.graph S x y) :
    ∃ (R : Set V) (hRS : R ⊆ S),
      IsMinimalClosedSeparator A R
        (outsideCutMap hRS x) (outsideCutMap hRS y) := by
  classical
  let Good : Set V → Prop := fun R =>
    ∃ hRS : R ⊆ S,
      A.IsClosed R ∧
        ¬ ReachOutside A.graph R
          (outsideCutMap hRS x) (outsideCutMap hRS y)
  let sizes : Set ℕ :=
    {n | ∃ R : Set V, Good R ∧ R.ncard = n}
  have hSgood : Good S := by
    refine ⟨Set.Subset.rfl, hSclosed, ?_⟩
    simpa [outsideCutMap] using hSep
  have hSizes : sizes.Nonempty := by
    exact ⟨S.ncard, S, hSgood, rfl⟩
  have hMin : sInf sizes ∈ sizes := Nat.sInf_mem hSizes
  obtain ⟨R, ⟨hRS, hRclosed, hRsep⟩, hCard⟩ := hMin
  refine ⟨R, hRS, hRclosed, hRsep, ?_⟩
  intro T hTclosed hTR hNoReach
  by_contra hRnotT
  have hTS : T ⊆ S := hTR.trans hRS
  have hTgood : Good T := by
    refine ⟨hTS, hTclosed, ?_⟩
    simpa [outsideCutMap] using hNoReach
  have hTsize : T.ncard ∈ sizes := ⟨T, hTgood, rfl⟩
  have hMinCard : R.ncard ≤ T.ncard := by
    rw [hCard]
    exact Nat.sInf_le hTsize
  have hTneR : T ≠ R := by
    intro hEq
    apply hRnotT
    simpa [hEq] using (Set.Subset.rfl : R ⊆ R)
  have hProper : T ⊂ R :=
    (Set.ssubset_iff_subset_ne).mpr ⟨hTR, hTneR⟩
  have hLess : T.ncard < R.ncard := Set.ncard_lt_ncard hProper
  exact (Nat.not_lt_of_ge hMinCard) hLess

end AllThoseRamseyClasses.Lifts
