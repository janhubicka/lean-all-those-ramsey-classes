import AllThoseRamseyClasses.Published.ProjectedBoundaryHullGlue2019
import PartiteConstruction.Ramsey.ClosureIrreducibleHulls

/-!
# Two ordinary irreducible free pieces suffice, with no size or rank bound

A weak source F embeds into a closed B-covered ambient C. Suppose two
ordinary irreducible induced source pieces freely cover F. Their actual
ambient closure hulls are closed U-irreducible, hence embed into B and
belong to K by closed heredity. The projected-boundary saturation theorem
completes F over the closure of the exact intersection.

Neither source piece, the intersection, nor F must be intrinsically
closed. The intersection need not be ordinarily irreducible. No bound
on cardinality, generating rank, or native active histories is assumed.
This is a proved completion criterion once this module passes CI, not
an assertion that all native source tests have such a two-piece cover.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Every embedded weak free union of TWO ordinary irreducible pieces
has a corrected K-completion in a closed ambient with original B-coverage.
The common weak intersection is allowed to be reducible and nonclosed. -/
theorem inducedClosed2019_weak_two_irreducible_cover_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {X Y UB : Type v} [Finite Y]
    (Source : RelStructure L X) (C : RelStructure L Y)
    (B : RelStructure L UB)
    (hC : IsUClosed rules C) (hBK : K B)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {Z : Type v} (A : RelStructure L Z), K A → A.Irreducible)
    (hCoverB : ∀ {Z : Type v} (Test : RelStructure L Z),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test C → Nonempty (Embedding Test B))
    (e : Embedding Source C)
    (S T : Set X)
    (hCover : ∀ x, x ∈ S ∨ x ∈ T)
    (hTuples : ∀ R (z : Fin (L.arity R) → X), Source.rel R z →
      (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T))
    (hS : (Source.induce S).Irreducible)
    (hT : (Source.induce T).Irreducible) :
    HasInducedClosedUKCompletion K rules Source := by
  classical
  let eS : Embedding (Source.induce S) C := e.comp (inclusion Source S)
  let eT : Embedding (Source.induce T) C := e.comp (inclusion Source T)
  have hRangeS : Set.range eS = e '' S := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hRangeT : Set.range eT = e '' T := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hSeedS : (C.induce (e '' S)).Irreducible := by
    rw [← hRangeS]
    exact hS.range_embedding eS
  have hSeedT : (C.induce (e '' T)).Irreducible := by
    rw [← hRangeT]
    exact hT.range_embedding eT
  let HS := UClosureHull rules C (e '' S)
  let HT := UClosureHull rules C (e '' T)
  have hHSClosed : IsUClosed rules (C.induce HS) :=
    hC.induce_UClosureHull (e '' S)
  have hHTClosed : IsUClosed rules (C.induce HT) :=
    hC.induce_UClosureHull (e '' T)
  have hHSIrred : IsUIrreducible rules (C.induce HS) :=
    hC.irreducibleSeed_hull_isUIrreducible (e '' S) hSeedS
  have hHTIrred : IsUIrreducible rules (C.induce HT) :=
    hC.irreducibleSeed_hull_isUIrreducible (e '' T) hSeedT
  obtain ⟨bS⟩ := hCoverB (C.induce HS) hHSClosed hHSIrred (inclusion C HS)
  obtain ⟨bT⟩ := hCoverB (C.induce HT) hHTClosed hHTIrred (inclusion C HT)
  have hHKS : K (C.induce HS) := hHer (C.induce HS) B hBK hHSClosed bS
  have hHKT : K (C.induce HT) := hHer (C.induce HT) B hBK hHTClosed bT
  have hCompS : HasInducedClosedUKCompletion K rules (C.induce HS) :=
    (inducedClosedKCompletion_iff_abstract_2019).mpr
      ⟨HS, inferInstance, C.induce HS, hHKS, hKIrr _ hHKS,
        Embedding.id (C.induce HS),
        (Embedding.id (C.induce HS)).isClosedUHomomorphismEmbedding rules⟩
  have hCompT : HasInducedClosedUKCompletion K rules (C.induce HT) :=
    (inducedClosedKCompletion_iff_abstract_2019).mpr
      ⟨HT, inferInstance, C.induce HT, hHKT, hKIrr _ hHKT,
        Embedding.id (C.induce HT),
        (Embedding.id (C.induce HT)).isClosedUHomomorphismEmbedding rules⟩
  apply inducedClosed2019_completion_of_projected_hull_cut
    Source C e
    (IsClosedUHomomorphismEmbedding.toInducedClosed
      (e.isClosedUHomomorphismEmbedding rules))
    S T hCover hTuples (C.induce HS) hHKS hHSClosed hC
    (inclusion C HS) ?_ hStrong hHer hKIrr hCompS hCompT
  intro x hxS _
  exact ⟨⟨e x, subset_UClosureHull rules C (e '' S) ⟨x, hxS, rfl⟩⟩, rfl⟩

end AllThoseRamseyClasses.Published
