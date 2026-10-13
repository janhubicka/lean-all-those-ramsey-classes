import AllThoseRamseyClasses.Published.NativePositivePullbackFreeCut2019

/-!
# Exact free covers iff original SOURCE tuples localize to a side

The corrected 2019 Lemma 2.30 may pull back a genuine native
copy/rest cover under a noninjective positive map. But two arbitrarily
selected transverse Hales--Jewett line images do NOT automatically
make a free cover of the coordinate core (the separate Boolean
crossing regression is CI-green PR #170).

This file states the exact and elementary condition ON THE ORIGINAL
WEAK SOURCE that makes two literal induced source subsets S,T form
a genuine relational free amalgam:

  (i) S∪T covers ALL original vertices, and
  (ii) EVERY original relation tuple is wholly in S OR wholly in T.

Both directions are proved. The overlap/root is the ACTUAL induced
intersection S∩T; it is NOT replaced by a closure hull, and neither
side nor source needs intrinsic U-closedness.

The theorem makes source tuple-localization a NECESSARY as well as
sufficient condition. Its negative companion shows that a single
actual relation tuple crossing the two exclusive sides prevents
that particular free cover, regardless of parameter transversality.
Neither theorem implies the general 2019 successor Picture
automatically has the required localization; the full Lemma 2.30
and Theorem 2.18 remain open.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- On the ORIGINAL exact relational source, the literal induced
two-side cover is a full relational free amalgam IFF all source
vertices and EVERY source relation tuple are local to the sides.

This is the converse missing from the positive free-cover pullback
lemma. The root is exactly the induced intersection S∩T. -/
theorem exact2019_free_cover_iff_source_tuple_local
    {U : Type v}
    (A : RelStructure L U) (S T : Set U) :
    IsFreeAmalgam
      (exactFreeCoverRootToLeft A S T)
      (exactFreeCoverRootToRight A S T)
      (inclusion A S) (inclusion A T) ↔
      (∀ u : U, u ∈ S ∨ u ∈ T) ∧
      (∀ R (z : Fin (L.arity R) → U),
        A.rel R z →
          (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T)) := by
  constructor
  · intro h
    constructor
    · intro u
      rcases h.covers u with ⟨x, hx⟩ | ⟨y, hy⟩
      · have heq : u = x.1 := hx
        exact Or.inl (heq ▸ x.2)
      · have heq : u = y.1 := hy
        exact Or.inr (heq ▸ y.2)
    · intro R z hz
      rcases (h.rel_iff R z).mp hz with
          ⟨x, _, hx⟩ | ⟨y, _, hy⟩
      · left
        intro k
        have hVal : z k = (x k).1 := congrFun hx k
        exact hVal ▸ (x k).2
      · right
        intro k
        have hVal : z k = (y k).1 := congrFun hy k
        exact hVal ▸ (y k).2
  · rintro ⟨hCover, hTuples⟩
    have hId : A.IsHomomorphism A (fun x : U => x) := by
      intro R z hz
      exact hz
    simpa only [Set.preimage_id] using
      (positive2019_pullback_exact_free_cover
        (f := fun x : U => x) hId S T hCover hTuples)

/-- One original positive relation tuple not wholly in EITHER
selected source side proves that these two exact induced sides
do NOT form a relational free amalgam.

This justifies the explicit tuple-localization hypothesis used
by CI-green two-copy native completion PR #172. -/
theorem exact2019_not_free_of_crossing_source_tuple
    {U : Type v}
    (A : RelStructure L U) (S T : Set U)
    (hCross : ∃ R (z : Fin (L.arity R) → U),
      A.rel R z ∧
      ¬ (∀ k, z k ∈ S) ∧
      ¬ (∀ k, z k ∈ T)) :
    ¬ IsFreeAmalgam
      (exactFreeCoverRootToLeft A S T)
      (exactFreeCoverRootToRight A S T)
      (inclusion A S) (inclusion A T) := by
  intro hFree
  obtain ⟨R, z, hz, hNotS, hNotT⟩ := hCross
  have hTuples :=
    (exact2019_free_cover_iff_source_tuple_local A S T).mp hFree
  rcases hTuples.2 R z hz with hS | hT
  · exact hNotS hS
  · exact hNotT hT

end AllThoseRamseyClasses.Published
