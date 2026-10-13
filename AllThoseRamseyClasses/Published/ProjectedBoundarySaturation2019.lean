import AllThoseRamseyClasses.Published.ExactFreeCoverTupleLocalization2019
import AllThoseRamseyClasses.Published.InducedClosed2019MixedCut
import PartiteConstruction.Ramsey.ClosureRelativeMapGlue

/-!
# Projected boundary saturation removes source-side closedness assumptions

For a genuine free source cover S,T and a positive map p into D, let H
be a relatively U-closed TARGET set containing p(S intersect T).
The enlarged source sides S union p^-1(H) and T union p^-1(H) are
relatively U-closed and freely cover the SAME original source.
Their intersection is exactly p^-1(H). Neither the source nor its
original cut is assumed intrinsically closed; p need not be injective.

If H is already contained in the projected closed hull of a source
side, saturation does not enlarge that projected hull. Thus it costs
no ADDITIONAL projected rank beyond the original side hull. This does
not assert that the original hull has small rank.

A common closed K-member D|H embedded in two independently completable
target sets now yields a completion of the ORIGINAL weak source. The
actual full embeddings on H are supplied by the protected completion
maps, not by an arbitrary possibly noninjective root completion.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Saturating a side by the preimage of a closed target boundary
makes it relatively U-closed. Only positive tuples are needed. -/
theorem positive2019_boundary_saturates_left
    {rules : ClosureDescription L} {X Y : Type v}
    (Source : RelStructure L X) (D : RelStructure L Y)
    (p : X → Y) (hp : Source.IsHomomorphism D p)
    (S T : Set X) (H : Set Y)
    (hH : IsUSubstructure rules D H)
    (hOverlap : ∀ x, x ∈ S → x ∈ T → p x ∈ H)
    (hTuples : ∀ R (z : Fin (L.arity R) → X), Source.rel R z →
      (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T)) :
    IsUSubstructure rules Source (S ∪ p ⁻¹' H) := by
  intro rule hrule z hz hRoot k
  rcases hTuples rule.symbol z hz with hS | hT
  · exact Or.inl (hS k)
  · right
    apply hH rule hrule (p ∘ z) (hp rule.symbol z hz) ?_ k
    intro a
    rcases hRoot a with haS | haH
    · exact hOverlap _ haS (hT (a.castLE rule.rootLE))
    · exact haH

/-- Saturation leaves the original projected closure hull unchanged
whenever that hull already contains the target boundary. This is
an equality of HULLS, not a bound on their generating ranks. -/
theorem projected2019_saturation_preserves_hull
    {rules : ClosureDescription L} {X Y : Type v}
    (D : RelStructure L Y) (p : X → Y)
    (S : Set X) (H : Set Y)
    (hH : H ⊆ UClosureHull rules D (p '' S)) :
    UClosureHull rules D (p '' (S ∪ p ⁻¹' H)) =
      UClosureHull rules D (p '' S) := by
  apply Set.Subset.antisymm
  · apply UClosureHull_minimal rules D
      (UClosureHull_isUSubstructure rules D (p '' S))
    rintro y ⟨x, hx, rfl⟩
    rcases hx with hxS | hxH
    · exact subset_UClosureHull rules D (p '' S) ⟨x, hxS, rfl⟩
    · exact hH hxH
  · apply UClosureHull_mono rules D
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, Or.inl hx, rfl⟩

/-- Genuine free source covers, with no source closedness assumptions,
glue after saturation along ONE closed K-boundary in a common target D.
The side targets L0,R0 may themselves be weak and are independently
completed. Their full embeddings of D|H force compatible boundary maps.
No additional extension or compatible-completion oracle is assumed. -/
theorem inducedClosed2019_completion_of_saturated_projected_cover
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L} {X Y : Type v} [Finite Y]
    (Source : RelStructure L X) (D : RelStructure L Y)
    (p : X → Y)
    (hp : IsInducedClosedUHomomorphismEmbedding rules Source D p)
    (S T : Set X)
    (hCover : ∀ x, x ∈ S ∨ x ∈ T)
    (hTuples : ∀ R (z : Fin (L.arity R) → X), Source.rel R z →
      (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T))
    (H L0 R0 : Set Y)
    (hHRelative : IsUSubstructure rules D H)
    (hHClosed : IsUClosed rules (D.induce H))
    (hHK : K (D.induce H))
    (hHL : H ⊆ L0) (hHR : H ⊆ R0)
    (hOverlap : ∀ x, x ∈ S → x ∈ T → p x ∈ H)
    (hLeft : ∀ x, x ∈ S → p x ∈ L0)
    (hRight : ∀ x, x ∈ T → p x ∈ R0)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hKIrr : ∀ {Z : Type v} (A : RelStructure L Z), K A → A.Irreducible)
    (hLC : HasInducedClosedUKCompletion K rules (D.induce L0))
    (hRC : HasInducedClosedUKCompletion K rules (D.induce R0)) :
    HasInducedClosedUKCompletion K rules Source := by
  classical
  have hpAbs := IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hp
  let SL : Set X := S ∪ p ⁻¹' H
  let SR : Set X := T ∪ p ⁻¹' H
  have hSL : IsUSubstructure rules Source SL :=
    positive2019_boundary_saturates_left Source D p hpAbs.1 S T H
      hHRelative hOverlap hTuples
  have hSR : IsUSubstructure rules Source SR :=
    positive2019_boundary_saturates_left Source D p hpAbs.1 T S H
      hHRelative (fun x hxT hxS => hOverlap x hxS hxT)
      (fun R z hz => (hTuples R z hz).symm)
  have hSLCover : ∀ x, x ∈ SL ∨ x ∈ SR := by
    intro x
    rcases hCover x with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr (Or.inl hx)
  have hSLTuples : ∀ R (z : Fin (L.arity R) → X), Source.rel R z →
      (∀ k, z k ∈ SL) ∨ (∀ k, z k ∈ SR) := by
    intro R z hz
    rcases hTuples R z hz with hS | hT
    · exact Or.inl (fun k => Or.inl (hS k))
    · exact Or.inr (fun k => Or.inl (hT k))
  have hFree :=
    (exact2019_free_cover_iff_source_tuple_local Source SL SR).mpr
      ⟨hSLCover, hSLTuples⟩
  have hRangeL : Set.range (inclusion Source SL) = SL := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact z.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hRangeR : Set.range (inclusion Source SR) = SR := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact z.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hSLRange : IsUSubstructure rules Source (Set.range (inclusion Source SL)) := by
    rw [hRangeL]
    exact hSL
  have hSRRange : IsUSubstructure rules Source (Set.range (inclusion Source SR)) := by
    rw [hRangeR]
    exact hSR
  have hMapL : ∀ x : SL, p x.1 ∈ L0 := by
    intro x
    rcases x.2 with hx | hx
    · exact hLeft x.1 hx
    · exact hHL hx
  have hMapR : ∀ x : SR, p x.1 ∈ R0 := by
    intro x
    rcases x.2 with hx | hx
    · exact hRight x.1 hx
    · exact hHR hx
  let pL : SL → L0 := fun x => ⟨p x.1, hMapL x⟩
  let pR : SR → R0 := fun x => ⟨p x.1, hMapR x⟩
  have hpLHom : (Source.induce SL).IsHomomorphism (D.induce L0) pL := by
    intro R z hz
    exact hpAbs.1 R (Subtype.val ∘ z) hz
  have hpRHom : (Source.induce SR).IsHomomorphism (D.induce R0) pR := by
    intro R z hz
    exact hpAbs.1 R (Subtype.val ∘ z) hz
  have hLInc : (D.induce L0).IsHomomorphism D (Subtype.val : L0 → Y) :=
    fun _ _ hz => hz
  have hRInc : (D.induce R0).IsHomomorphism D (Subtype.val : R0 → Y) :=
    fun _ _ hz => hz
  have hpL : IsClosedUHomomorphismEmbedding rules
      (Source.induce SL) (D.induce L0) pL :=
    IsClosedUHomomorphismEmbedding.of_comp_homomorphisms hpLHom hLInc
      (hpAbs.comp ((inclusion Source SL).isClosedUHomomorphismEmbedding rules))
  have hpR : IsClosedUHomomorphismEmbedding rules
      (Source.induce SR) (D.induce R0) pR :=
    IsClosedUHomomorphismEmbedding.of_comp_homomorphisms hpRHom hRInc
      (hpAbs.comp ((inclusion Source SR).isClosedUHomomorphismEmbedding rules))
  have hRootMap : ∀ x : SL ∩ SR, p x.1 ∈ H := by
    intro x
    rcases x.2.1 with hxS | hxH
    · rcases x.2.2 with hxT | hxH
      · exact hOverlap x.1 hxS hxT
      · exact hxH
    · exact hxH
  let q : (SL ∩ SR) → H := fun x => ⟨p x.1, hRootMap x⟩
  let aL : Embedding (D.induce H) (D.induce L0) := {
    toFun := fun x => ⟨x.1, hHL x.2⟩
    injective := by
      intro x y h
      exact Subtype.ext (congrArg Subtype.val h)
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let aR : Embedding (D.induce H) (D.induce R0) := {
    toFun := fun x => ⟨x.1, hHR x.2⟩
    injective := by
      intro x y h
      exact Subtype.ext (congrArg Subtype.val h)
    map_rel_iff := fun _ _ => Iff.rfl
  }
  obtain ⟨XL, hXL, TL, hTL, _, fL, hfL⟩ :=
    (inducedClosedKCompletion_iff_abstract_2019).mp hLC
  obtain ⟨YR, hYR, TR, hTR, _, fR, hfR⟩ :=
    (inducedClosedKCompletion_iff_abstract_2019).mp hRC
  letI : Finite XL := hXL
  letI : Finite YR := hYR
  obtain ⟨eL, eR, heL, heR⟩ :=
    IsClosedUHomomorphismEmbedding.common_boundary_embeddings
      hHClosed (hKIrr (D.induce H) hHK) aL aR hfL hfR
  obtain ⟨Z, hZ, Target, hTarget, jL, jR, hGlue, _⟩ :=
    hStrong (D.induce H) TL TR hHK hTL hTR eL eR
  let gL : SL → Z := jL ∘ (fL ∘ pL)
  let gR : SR → Z := jR ∘ (fR ∘ pR)
  have hgL : IsClosedUHomomorphismEmbedding rules (Source.induce SL) Target gL :=
    (jL.isClosedUHomomorphismEmbedding rules).comp (hfL.comp hpL)
  have hgR : IsClosedUHomomorphismEmbedding rules (Source.induce SR) Target gR :=
    (jR.isClosedUHomomorphismEmbedding rules).comp (hfR.comp hpR)
  have hRootL : ∀ r : SL ∩ SR,
      pL (exactFreeCoverRootToLeft Source SL SR r) = aL (q r) :=
    fun _ => Subtype.ext rfl
  have hRootR : ∀ r : SL ∩ SR,
      pR (exactFreeCoverRootToRight Source SL SR r) = aR (q r) :=
    fun _ => Subtype.ext rfl
  have hCompat : ∀ r : SL ∩ SR,
      gL (exactFreeCoverRootToLeft Source SL SR r) =
        gR (exactFreeCoverRootToRight Source SL SR r) := by
    intro r
    calc
      gL (exactFreeCoverRootToLeft Source SL SR r) = jL (fL (aL (q r))) :=
        congrArg (fun x => jL (fL x)) (hRootL r)
      _ = jL (eL (q r)) := congrArg jL (heL (q r)).symm
      _ = jR (eR (q r)) := hGlue (q r)
      _ = jR (fR (aR (q r))) := congrArg jR (heR (q r))
      _ = gR (exactFreeCoverRootToRight Source SL SR r) :=
        congrArg (fun x => jR (fR x)) (hRootR r).symm
  have hAbs : HasClosedUKCompletion K rules Source :=
    ⟨Z, hZ, Target, hTarget, hKIrr Target hTarget,
      hFree.compatibleFold gL gR hCompat,
      IsClosedUHomomorphismEmbedding.fold_free_of_relative_ranges
        hFree hSLRange hSRRange gL gR hgL hgR hCompat⟩
  exact (inducedClosedKCompletion_iff_abstract_2019).mpr hAbs

end AllThoseRamseyClasses.Published
