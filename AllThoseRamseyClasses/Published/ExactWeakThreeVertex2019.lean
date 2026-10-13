import AllThoseRamseyClasses.Published.ThreeVertexFreeCover2019
import AllThoseRamseyClasses.Published.ExactWeakTwoIrreducibleCover2019
import AllThoseRamseyClasses.Published.ExactWeakTwoVertex2019

/-!
# Every exact weak THREE-vertex test has a corrected completion

The new saturation argument handles the connected reducible case as a
free union of two ordinary irreducible pieces, even when their common
singleton is not intrinsically closed. A disconnected source splits over
its literal empty root; exact weak two-vertex completions suffice there.
The irreducible case is already supplied by ambient closed B-coverage.

The original weak carrier is preserved throughout. No Hales--Jewett
geometry, source closedness, or external closed-rank invariant is assumed.
Cardinality three is NOT generating rank three.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Restrict a corrected completion along a full embedding, without
changing its finite K-target or extending a weak-source map to a hull. -/
theorem inducedClosed2019_pullback_completion_embedding
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L}
    {X Y : Type v} {Source : RelStructure L X} {D : RelStructure L Y}
    (e : Embedding Source D) (h : HasInducedClosedUKCompletion K rules D) :
    HasInducedClosedUKCompletion K rules Source := by
  obtain ⟨Z, hZ, Target, hK, hIrr, f, hf⟩ :=
    (inducedClosedKCompletion_iff_abstract_2019).mp h
  exact (inducedClosedKCompletion_iff_abstract_2019).mpr
    ⟨Z, hZ, Target, hK, hIrr, f ∘ e,
      hf.comp (e.isClosedUHomomorphismEmbedding rules)⟩

/-- The verified exact two-vertex theorem on an arbitrary embedded
carrier, obtained through its literal finite image, not its closure. -/
theorem inducedClosed2019_embedded_weak_card_le_two_completion
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L}
    {X Y UB : Type v} [Fintype X] [Finite Y] [Finite UB]
    (Source : RelStructure L X) (C : RelStructure L Y) (B : RelStructure L UB)
    (hC : IsUClosed rules C) (hBK : K B)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {Z : Type v} (A : RelStructure L Z), K A → A.Irreducible)
    (hCoverB : ∀ {Z : Type v} (Test : RelStructure L Z),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test C → Nonempty (Embedding Test B))
    (e : Embedding Source C) (hCard : Fintype.card X ≤ 2) :
    HasInducedClosedUKCompletion K rules Source := by
  classical
  let T : Finset Y := Finset.univ.image e
  have hTCard : T.card ≤ 2 :=
    Finset.card_image_le.trans (by simpa using hCard)
  let f : Embedding Source (C.induce (↑T : Set Y)) := {
    toFun := fun x => ⟨e x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
    injective := by
      intro x y h
      exact e.injective (congrArg (fun z : (↑T : Set Y) => z.1) h)
    map_rel_iff := fun R z => e.map_rel_iff R z
  }
  exact inducedClosed2019_pullback_completion_embedding f
    (inducedClosed2019_exact_weak_card_le_two_completion
      C B hC hBK hStrong hHer hKIrr hCoverB T hTCard)

/-- A disjoint genuine free cover glues from its two corrected weak
completions. The empty root's actual relational signature is certified
by the original B-coverage, so nullary data are not ignored. No source
or side intrinsic closedness is needed. -/
theorem inducedClosed2019_disjoint_weak_cover_completion
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L}
    {X Y UB : Type v} [Finite X]
    (Source : RelStructure L X) (C : RelStructure L Y) (B : RelStructure L UB)
    (hBK : K B) (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {Z : Type v} (A : RelStructure L Z), K A → A.Irreducible)
    (hCoverB : ∀ {Z : Type v} (Test : RelStructure L Z),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test C → Nonempty (Embedding Test B))
    (e : Embedding Source C) (S T : Set X)
    (hCover : ∀ x, x ∈ S ∨ x ∈ T)
    (hTuples : ∀ R (z : Fin (L.arity R) → X), Source.rel R z →
      (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T))
    (hDisjoint : Disjoint S T)
    (hLC : HasInducedClosedUKCompletion K rules (Source.induce S))
    (hRC : HasInducedClosedUKCompletion K rules (Source.induce T)) :
    HasInducedClosedUKCompletion K rules Source := by
  have hEmptyClosed : IsUClosed rules (Source.induce (∅ : Set X)) := by
    intro rule _
    constructor
    · intro t _
      exact False.elim (t ((⟨0, rule.rootPositive⟩ : Fin rule.rootSize).castLE
        rule.rootLE)).2
    · intro f
      exact False.elim (f ⟨0, rule.rootPositive⟩).2
  have hEmptyRelative : IsUSubstructure rules Source (∅ : Set X) := by
    intro rule _ t _ hRoot k
    exact False.elim (hRoot ⟨0, rule.rootPositive⟩)
  have hEmptyIrred : (Source.induce (∅ : Set X)).Irreducible := by
    intro x y _
    exact x.2.elim
  obtain ⟨eB⟩ := hCoverB (Source.induce (∅ : Set X)) hEmptyClosed
    (hEmptyIrred.isUIrreducible rules) (e.comp (inclusion Source (∅ : Set X)))
  have hEmptyK : K (Source.induce (∅ : Set X)) :=
    hHer (Source.induce (∅ : Set X)) B hBK hEmptyClosed eB
  exact inducedClosed2019_completion_of_saturated_projected_cover
    Source Source (fun x : X => x)
    (IsClosedUHomomorphismEmbedding.toInducedClosed
      ((Embedding.id Source).isClosedUHomomorphismEmbedding rules))
    S T hCover hTuples (∅ : Set X) S T
    hEmptyRelative hEmptyClosed hEmptyK (Set.empty_subset S) (Set.empty_subset T)
    (fun x hxS hxT => False.elim (Set.disjoint_left.mp hDisjoint hxS hxT))
    (fun x hx => hx) (fun x hx => hx) hStrong hKIrr hLC hRC

/-- Every weak structure on at most THREE vertices fully embedded in
a finite closed B-covered ambient has a corrected K-completion.
There is no restriction to maximal intrinsic rank or native histories. -/
theorem inducedClosed2019_embedded_weak_card_le_three_completion
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L}
    {X Y UB : Type v} [Fintype X] [Finite Y] [Finite UB]
    (Source : RelStructure L X) (C : RelStructure L Y) (B : RelStructure L UB)
    (hC : IsUClosed rules C) (hBK : K B)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {Z : Type v} (A : RelStructure L Z), K A → A.Irreducible)
    (hCoverB : ∀ {Z : Type v} (Test : RelStructure L Z),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test C → Nonempty (Embedding Test B))
    (e : Embedding Source C) (hCard : Fintype.card X ≤ 3) :
    HasInducedClosedUKCompletion K rules Source := by
  classical
  by_cases hIrred : Source.Irreducible
  · have hRange : HasInducedClosedUKCompletion K rules
        (C.induce (Set.range e)) :=
      (inducedClosedKCompletion_iff_abstract_2019).mpr
        (weak_irreducible_completion_of_closed_coverage
          hC hBK (hKIrr B hBK) hCoverB (Set.range e) (hIrred.range_embedding e))
    exact inducedClosed2019_pullback_completion_embedding (inducedRangeEmbedding e) hRange
  · obtain ⟨S, T, hCover, hTuples, hCases⟩ :=
      exact2019_three_vertex_free_cover_dichotomy Source hCard hIrred
    rcases hCases with ⟨hDisjoint, hSCard, hTCard⟩ | ⟨hS, hT⟩
    · letI : Fintype S := Fintype.ofFinite S
      letI : Fintype T := Fintype.ofFinite T
      have hSC : Fintype.card S ≤ 2 := by
        simpa only [Nat.card_eq_fintype_card] using hSCard
      have hTC : Fintype.card T ≤ 2 := by
        simpa only [Nat.card_eq_fintype_card] using hTCard
      have hLC : HasInducedClosedUKCompletion K rules (Source.induce S) :=
        inducedClosed2019_embedded_weak_card_le_two_completion
          (Source.induce S) C B hC hBK hStrong hHer hKIrr hCoverB
          (e.comp (inclusion Source S)) hSC
      have hRC : HasInducedClosedUKCompletion K rules (Source.induce T) :=
        inducedClosed2019_embedded_weak_card_le_two_completion
          (Source.induce T) C B hC hBK hStrong hHer hKIrr hCoverB
          (e.comp (inclusion Source T)) hTC
      exact inducedClosed2019_disjoint_weak_cover_completion
        Source C B hBK hStrong hHer hKIrr hCoverB e S T hCover hTuples hDisjoint hLC hRC
    · exact inducedClosed2019_weak_two_irreducible_cover_completion
        Source C B hC hBK hStrong hHer hKIrr hCoverB e S T hCover hTuples hS hT

/-- Exact original induced-test formulation: all weak vertex sets of
size at most three complete in a closed B-covered Picture. -/
theorem inducedClosed2019_exact_weak_card_le_three_completion
    {K : StructureClass.{u,v} (L := L)} {rules : ClosureDescription L}
    {Y UB : Type v} [Finite Y] [Finite UB]
    (C : RelStructure L Y) (B : RelStructure L UB)
    (hC : IsUClosed rules C) (hBK : K B)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {Z : Type v} (A : RelStructure L Z), K A → A.Irreducible)
    (hCoverB : ∀ {Z : Type v} (Test : RelStructure L Z),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test C → Nonempty (Embedding Test B))
    (S : Finset Y) (hCard : S.card ≤ 3) :
    HasInducedClosedUKCompletion K rules (C.induce (↑S : Set Y)) := by
  exact inducedClosed2019_embedded_weak_card_le_three_completion
    (C.induce (↑S : Set Y)) C B hC hBK hStrong hHer hKIrr hCoverB
    (inclusion C (↑S : Set Y)) (by simpa using hCard)

end AllThoseRamseyClasses.Published
