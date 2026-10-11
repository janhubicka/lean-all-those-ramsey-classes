import PartiteConstruction.Ramsey.ClosureGeneratedHullRank

/-!
# 2019 Lemma 2.30: minimum generators and proper saturated side cuts

The higher-rank Picture proof needs to split a PRESCRIBED closed
generated hull into proper sides. A free split of its smaller exact
weak generating set does not automatically survive closure:
saturating a side may absorb a generator from the other side.

The valid rank-theoretic criterion is that EVERY vertex x of a
minimum finite U-generating set G is essential:

    x ∉ cl_U^A(G \ {x}).

Therefore any proposed side seed S CONTAINED in the hull of the
other generators remains proper after closure saturation:
    x ∉ cl_U^A(S).

The property holds for arbitrary finite relational sources in
the actual 2019 U-closure and U-size language, including weak
non-U-closed structures. No substitute closure of the tested
weak source is used.

This is an independent reproduction of the elementary argument
developed in partite-construction draft PR #240, rechecked against
the pinned 2019 dependency and audited separately.

The unproved geometric premise for the general native Hales--
Jewett rank increment is that the actual chosen copy/rest side
SEED lies in such a proper hull. Without that containment,
minimum rank alone does not justify the 2019 free-cut induction.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- Every member of a MINIMUM generating set G is indispensable:
it cannot be generated from the remaining members of G.

No U-closedness of the ambient or seed structure is assumed. -/
theorem minimal2019_generator_not_in_erase_hull
    [Fintype V]
    (rules : ClosureDescription L) (A : RelStructure L V)
    (G : Finset V)
    (hGen : IsUGenerating rules A (↑G : Set V))
    (hMin : G.card = USize rules A)
    (x : V) (hx : x ∈ G) :
    x ∉ UClosureHull rules A (↑(G.erase x) : Set V) := by
  classical
  intro hxHull
  let H : Set V := UClosureHull rules A (↑(G.erase x) : Set V)
  have hHClosed : IsUSubstructure rules A H :=
    UClosureHull_isUSubstructure rules A (↑(G.erase x) : Set V)
  have hGsubset : (↑G : Set V) ⊆ H := by
    intro y hy
    by_cases hyx : y = x
    · subst y
      exact hxHull
    · exact subset_UClosureHull rules A
        (↑(G.erase x) : Set V)
        (Finset.mem_erase.mpr ⟨hyx, hy⟩)
  have hEGen : IsUGenerating rules A
      (↑(G.erase x) : Set V) := by
    change H = Set.univ
    apply Set.eq_univ_of_forall
    intro y
    have hGenHull :
        y ∈ UClosureHull rules A (↑G : Set V) := by
      rw [hGen]
      trivial
    exact UClosureHull_minimal rules A hHClosed
      hGsubset hGenHull
  have hBound : USize rules A ≤ (G.erase x).card :=
    USize_le_of_generating rules A (G.erase x) hEGen
  have hCard : (G.erase x).card + 1 = G.card := by
    simpa using Finset.card_erase_of_mem hx
  omega

/-- If a proposed side seed is contained in the U-closure of all
minimum generators except one, saturating this seed remains proper.
The omitted essential generator cannot reappear.

This is only a sufficient criterion, not a theorem that arbitrary
core/rest pieces of an actual Hales--Jewett Picture satisfy it. -/
theorem minimal2019_generator_excluded_from_saturated_cut
    [Fintype V]
    (rules : ClosureDescription L) (A : RelStructure L V)
    (G : Finset V)
    (hGen : IsUGenerating rules A (↑G : Set V))
    (hMin : G.card = USize rules A)
    (x : V) (hx : x ∈ G)
    (S : Set V)
    (hSeed : S ⊆ UClosureHull rules A (↑(G.erase x) : Set V)) :
    x ∉ UClosureHull rules A S := by
  intro hxS
  have hHull : IsUSubstructure rules A
      (UClosureHull rules A (↑(G.erase x) : Set V)) :=
    UClosureHull_isUSubstructure rules A (↑(G.erase x) : Set V)
  have hIncluded : UClosureHull rules A S ⊆
      UClosureHull rules A (↑(G.erase x) : Set V) :=
    UClosureHull_minimal rules A hHull hSeed
  exact minimal2019_generator_not_in_erase_hull
    rules A G hGen hMin x hx (hIncluded hxS)

end AllThoseRamseyClasses.Published
