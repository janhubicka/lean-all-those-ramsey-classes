import AllThoseRamseyClasses.Published.ProjectedBoundarySaturation2019

/-!
# General projected-hull gluing with an arbitrary weak source separator

The old projected-cut theorem required intrinsic closedness of the
source root and semiclosed source sides. Both restrictions are removed
here by saturating the SOURCE COVER, not by replacing the tested source.
The new common boundary is the actual closure of the projected original
separator in D. Its K-membership follows from closed heredity inside
one specified closed A-copy. Independent side completions then agree
on this fixed boundary after strong amalgamation.

Both projected side hulls stay EXACTLY the original side hulls after
saturation. Accordingly the rank corollary requires only their original
absolute rank-j bounds. It neither assumes nor proves a bound for every
proper source cut. Extracting the suitable native cut and those bounds
is still needed for the unrestricted Picture increment.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Closing the projected original separator and saturating both
source sides adds no new projected closure points to either side. -/
theorem projected2019_separator_saturation_preserves_both_hulls
    {rules : ClosureDescription L} {X Y : Type v}
    (D : RelStructure L Y) (p : X → Y) (S T : Set X) :
    let H := UClosureHull rules D (p '' (S ∩ T))
    UClosureHull rules D (p '' (S ∪ p ⁻¹' H)) =
        UClosureHull rules D (p '' S) ∧
    UClosureHull rules D (p '' (T ∪ p ⁻¹' H)) =
        UClosureHull rules D (p '' T) := by
  dsimp only
  constructor
  · apply projected2019_saturation_preserves_hull
    apply UClosureHull_mono rules D
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx.1, rfl⟩
  · apply projected2019_saturation_preserves_hull
    apply UClosureHull_mono rules D
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx.2, rfl⟩

/-- Complete the ORIGINAL exact source from two original projected
side-hull completions. No source root/side/whole closedness or source
rank maximality is assumed. The projection need not be injective. -/
theorem inducedClosed2019_completion_of_projected_hull_cut
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L} {X Y VA : Type v} [Finite Y]
    (Source : RelStructure L X) (D : RelStructure L Y)
    (p : X → Y)
    (hp : IsInducedClosedUHomomorphismEmbedding rules Source D p)
    (S T : Set X)
    (hCover : ∀ x, x ∈ S ∨ x ∈ T)
    (hTuples : ∀ R (z : Fin (L.arity R) → X), Source.rel R z →
      (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T))
    (A : RelStructure L VA) (hKA : K A)
    (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (a : Embedding A D)
    (hSeparator : ∀ x, x ∈ S → x ∈ T → p x ∈ Set.range a)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {Z : Type v} (E : RelStructure L Z), K E → E.Irreducible)
    (hLeft : HasInducedClosedUKCompletion K rules
      (D.induce (UClosureHull rules D (p '' S))))
    (hRight : HasInducedClosedUKCompletion K rules
      (D.induce (UClosureHull rules D (p '' T)))) :
    HasInducedClosedUKCompletion K rules Source := by
  let H := UClosureHull rules D (p '' (S ∩ T))
  let DL := UClosureHull rules D (p '' S)
  let DR := UClosureHull rules D (p '' T)
  have hImage : p '' (S ∩ T) ⊆ Set.range a := by
    rintro y ⟨x, hx, rfl⟩
    exact hSeparator x hx.1 hx.2
  obtain ⟨hHK, _⟩ := closedHull_in_class_of_subset_copy K rules
    (fun {_ _} {E F} hF hE e => hHer E F hF hE e)
    hKIrr hKA hA hD a (p '' (S ∩ T)) hImage
  have hHL : H ⊆ DL := by
    apply UClosureHull_mono rules D
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx.1, rfl⟩
  have hHR : H ⊆ DR := by
    apply UClosureHull_mono rules D
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx.2, rfl⟩
  apply inducedClosed2019_completion_of_saturated_projected_cover
    Source D p hp S T hCover hTuples H DL DR
    (UClosureHull_isUSubstructure rules D (p '' (S ∩ T)))
    (hD.induce_UClosureHull (p '' (S ∩ T))) hHK hHL hHR
    ?_ ?_ ?_ hStrong hKIrr hLeft hRight
  · intro x hxS hxT
    exact subset_UClosureHull rules D (p '' (S ∩ T)) ⟨x, ⟨hxS, hxT⟩, rfl⟩
  · intro x hx
    exact subset_UClosureHull rules D (p '' S) ⟨x, hx, rfl⟩
  · intro x hx
    exact subset_UClosureHull rules D (p '' T) ⟨x, hx, rfl⟩

/-- The rank-j completion invariant applies to the ORIGINAL projected
side hulls. Saturation removes the source closedness assumptions without
altering either hull or its rank. Both numerical bounds remain explicit. -/
theorem inducedClosed2019_completion_of_projected_rank_cut_without_closed_root
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L} {X Y VA : Type v} [Finite Y]
    (Source : RelStructure L X) (D : RelStructure L Y)
    (p : X → Y)
    (hp : IsInducedClosedUHomomorphismEmbedding rules Source D p)
    (S T : Set X)
    (hCover : ∀ x, x ∈ S ∨ x ∈ T)
    (hTuples : ∀ R (z : Fin (L.arity R) → X), Source.rel R z →
      (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T))
    (A : RelStructure L VA) (hKA : K A)
    (hA : IsUClosed rules A) (hD : IsUClosed rules D)
    (a : Embedding A D)
    (hSeparator : ∀ x, x ∈ S → x ∈ T → p x ∈ Set.range a)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {Z : Type v} (E : RelStructure L Z), K E → E.Irreducible)
    (j : ℕ)
    [Fintype (UClosureHull rules D (p '' S))]
    [Fintype (UClosureHull rules D (p '' T))]
    (hRankL : USize rules (D.induce (UClosureHull rules D (p '' S))) ≤ j)
    (hRankR : USize rules (D.induce (UClosureHull rules D (p '' T))) ≤ j)
    (hRank : ∀ (Q : Set Y) [Fintype Q], IsUClosed rules (D.induce Q) →
      USize rules (D.induce Q) ≤ j →
      HasInducedClosedUKCompletion K rules (D.induce Q)) :
    HasInducedClosedUKCompletion K rules Source := by
  exact inducedClosed2019_completion_of_projected_hull_cut
    Source D p hp S T hCover hTuples A hKA hA hD a hSeparator
    hStrong hHer hKIrr
    (hRank _ (hD.induce_UClosureHull (p '' S)) hRankL)
    (hRank _ (hD.induce_UClosureHull (p '' T)) hRankR)

end AllThoseRamseyClasses.Published
