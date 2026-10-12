import AllThoseRamseyClasses.Published.NativePositivePullbackFreeCut2019

/-!
# 2019 native multi-attachment: TWO active private exteriors force a proper free cut

The proof of the strict rank-j+1 step must not infer properness of a selected
copy/rest decomposition merely from an abstract relational free cover.

Here the missing elementary witness calculation is carried out in the
ACTUAL simultaneous attachment, with no source closedness or global map
injectivity: a vertex projecting to the private exterior of copy j cannot
lie in any different attached old copy i. Consequently, TWO distinct
active copy indices i,j provide precisely the two exclusive-side witnesses
needed for the previously proved exact copy/rest free decomposition.
When the original exact weak source has <=j+1 vertices, the chosen source
cut is proper and BOTH induced sides have <=j vertices.

This does not establish that every exceptional native test activates
two copies, nor any A-root compatibility. These remain genuine obligations
for the corrected higher-rank Lemma 2.30 and main Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment

universe u v
variable {L : RelLanguage.{u}}

/-- A vertex in the PRIVATE exterior of index j cannot belong to the
genuine attached old-copy range of a different index i. -/
theorem native2019_other_private_not_in_chosen_copy
    {V W I : Type v}
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (i j : I) (hij : i ≠ j)
    (z : Vertex Support (W := W) (I := I))
    (hOtherPrivate : OutsideAt (W := W) (I := I) Support j z) :
    ¬ InCopy Old Support Core maps i z := by
  rintro ⟨y, hy⟩
  have hImpossible :
      ¬ OutsideAt (W := W) (I := I) Support j
        (copyMap Old Support Core maps i y) :=
    copyMap_not_outside_of_ne
      (B := Old) (S := Support) (D := Core) (f := maps)
      (i := j) i hij y
  rw [hy] at hOtherPrivate
  exact hImpossible hOtherPrivate

/-- The TWO distinct active private copy indices directly give a PROPER
free decomposition of the exact ORIGINAL source, even when the positive
projection is not injective and the native target is non-semi-closed. -/
theorem native2019_two_active_private_copies_proper
    {U V W I : Type v}
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphism (attach Old Support Core maps) p)
    (i j : I) (hij : i ≠ j)
    (hActiveI : ∃ x : U,
      OutsideAt (W := W) (I := I) Support i (p x))
    (hActiveJ : ∃ y : U,
      OutsideAt (W := W) (I := I) Support j (p y)) :
    Nonempty (ProperFreeDecomposition Source) := by
  have hBeyond : ∃ y : U,
      ¬ InCopy Old Support Core maps i (p y) := by
    obtain ⟨y, hy⟩ := hActiveJ
    exact ⟨y, native2019_other_private_not_in_chosen_copy
      Old Support Core maps i j hij (p y) hy⟩
  exact native2019_positive_source_copy_rest_proper
    Source Old Support Core maps p hp i hActiveI hBeyond

/-- A true two-active-line native history supplies absolute SMALL
source-side vertex bounds, with no generator-deletion rank shortcut.
No common A-root is supplied by this geometric lemma. -/
theorem native2019_two_active_private_copies_small_sides
    {U V W I : Type v}
    [Fintype U]
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphism (attach Old Support Core maps) p)
    (i j : I) (hij : i ≠ j)
    (rank : ℕ)
    (hCard : Fintype.card U ≤ rank + 1)
    (hActiveI : ∃ x : U,
      OutsideAt (W := W) (I := I) Support i (p x))
    (hActiveJ : ∃ y : U,
      OutsideAt (W := W) (I := I) Support j (p y)) :
    ∃ d : ProperFreeDecomposition Source,
      Nat.card d.Left ≤ rank ∧ Nat.card d.Right ≤ rank := by
  have hBeyond : ∃ y : U,
      ¬ InCopy Old Support Core maps i (p y) := by
    obtain ⟨y, hy⟩ := hActiveJ
    exact ⟨y, native2019_other_private_not_in_chosen_copy
      Old Support Core maps i j hij (p y) hy⟩
  exact native2019_positive_source_proper_cut_small_sides
    Source Old Support Core maps p hp i rank hCard hActiveI hBeyond

end AllThoseRamseyClasses.Published
