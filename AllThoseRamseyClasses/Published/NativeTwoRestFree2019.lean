import AllThoseRamseyClasses.Published.NativePositivePullbackFreeCut2019
import AllThoseRamseyClasses.Published.NativePositiveGeneratorIndices2019

/-!
# Two complementary REST pieces always form a genuine native free cover

An important distinction in the corrected 2019 Lemma 2.30:

* The two RANGES of transverse old-copy HJ lines need not form
  a relational free cover of their induced union. The CI-green
  Boolean coordinate-power crossing regression PR #170 proves this.
* The two complementary REST sets of distinct attached copy
  indices DO form a full genuine relational free cover of the
  native attachment: Rest(j) excludes ONLY private exterior
  vertices of copy j, and Rest(i) excludes ONLY private exterior
  vertices of copy i. All power CORE vertices belong to BOTH.

The proof is exact for the actual simultaneous attachment,
for every relation arity, any old attaching support (including
non-U-closed support), and any number of additional native copies.
Every tuple from the core lies in both rest sets; every tuple
coming from an attached copy k lies wholly in Rest(j) if k!=j,
or in Rest(i) if k=j (as i!=j).

Pulling back under ANY POSITIVE, possibly NONINJECTIVE source map
yields a genuine relational free amalgam of the two literal
original weak induced REST preimages.

If the original source meets the private exterior of BOTH i and j,
both rest preimages are PROPER. For a finite source of <=rank+1
vertices, each literal source side has <=rank vertices.

This resolves the RELATIONAL freeness/strict-size piece of the
two-active-line native history WITHOUT requiring tuple localization
to two HJ line RANGES, and is fully compatible with pure-core
crossing relation tuples.

It does NOT supply two OLD-Picture side maps on the rest sets:
these still require active-subhistory localization/coordinate
retractions. Moreover the common root now includes the ENTIRE
tested core, whose old coordinate images need NOT factor through
one embedded A-copy. Consequently the compatible closed K-boundary
and rank-j completion step remain OPEN, as does general
Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment

universe u v
variable {L : RelLanguage.{u}}

/-- For distinct native copy indices i,j, the two complementary
REST sets of the ACTUAL simultaneous attachment form a relational
free cover. This remains true for pure core relations crossing
exclusive HJ line ranges: core belongs to BOTH rests.

It pulls back under ANY positive source map, without injectivity,
source/attachment U-closedness, or finite index assumptions. -/
theorem native2019_positive_two_rest_source_free
    {U V W I : Type v}
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphism
      (attach Old Support Core maps) p)
    (i j : I) (hij : i ≠ j) :
    let LeftSet : Set U :=
      {x | ¬ OutsideAt (W := W) (I := I) Support j (p x)}
    let RightSet : Set U :=
      {x | ¬ OutsideAt (W := W) (I := I) Support i (p x)}
    IsFreeAmalgam
      (exactFreeCoverRootToLeft Source LeftSet RightSet)
      (exactFreeCoverRootToRight Source LeftSet RightSet)
      (inclusion Source LeftSet)
      (inclusion Source RightSet) := by
  classical
  let LeftTarget : Set (Vertex Support (W := W) (I := I)) :=
    {z | ¬ OutsideAt (W := W) (I := I) Support j z}
  let RightTarget : Set (Vertex Support (W := W) (I := I)) :=
    {z | ¬ OutsideAt (W := W) (I := I) Support i z}
  have hCover :
      ∀ z : Vertex Support (W := W) (I := I),
        z ∈ LeftTarget ∨ z ∈ RightTarget := by
    intro z
    by_cases hz : OutsideAt (W := W) (I := I) Support j z
    · right
      intro hi
      exact hij (native2019_private_exterior_index_unique Support hi hz)
    · exact Or.inl hz
  have hTuples :
      ∀ R (z : Fin (L.arity R) →
          Vertex Support (W := W) (I := I)),
        (attach Old Support Core maps).rel R z →
          (∀ k, z k ∈ LeftTarget) ∨
          (∀ k, z k ∈ RightTarget) := by
    intro R z hz
    rcases hz with ⟨ys, _, heq⟩ | ⟨k, ys, _, heq⟩
    · left
      intro t hOutside
      obtain ⟨x, hx⟩ := hOutside
      have hCore : z t = Sum.inl (ys t) := congrFun heq t
      rw [hx] at hCore
      cases hCore
    · by_cases hkj : k = j
      · subst k
        right
        intro t
        have hNot :
            ¬ OutsideAt (W := W) (I := I)
              Support i
              (copyMap Old Support Core maps j (ys t)) :=
          copyMap_not_outside_of_ne
            (B := Old) (S := Support) (D := Core) (f := maps)
            (i := i) j hij.symm (ys t)
        have hEq : z t = copyMap Old Support Core maps j (ys t) :=
          congrFun heq t
        simpa only [hEq] using hNot
      · left
        intro t
        have hNot :
            ¬ OutsideAt (W := W) (I := I)
              Support j
              (copyMap Old Support Core maps k (ys t)) :=
          copyMap_not_outside_of_ne
            (B := Old) (S := Support) (D := Core) (f := maps)
            (i := j) k hkj (ys t)
        have hEq : z t = copyMap Old Support Core maps k (ys t) :=
          congrFun heq t
        simpa only [hEq] using hNot
  exact positive2019_pullback_exact_free_cover
    hp LeftTarget RightTarget hCover hTuples

/-- Two private-active source copy indices make BOTH exact
complementary rest sides PROPER, even though ALL core vertices
are retained on BOTH sides. No closure of the source is used. -/
theorem native2019_two_private_active_rest_cut_proper
    {U V W I : Type v}
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphism
      (attach Old Support Core maps) p)
    (i j : I) (hij : i ≠ j)
    (hActiveI : ∃ x : U, OutsideAt
      (W := W) (I := I) Support i (p x))
    (hActiveJ : ∃ y : U, OutsideAt
      (W := W) (I := I) Support j (p y)) :
    Nonempty (ProperFreeDecomposition Source) := by
  classical
  let LeftSet : Set U :=
    {x | ¬ OutsideAt (W := W) (I := I) Support j (p x)}
  let RightSet : Set U :=
    {x | ¬ OutsideAt (W := W) (I := I) Support i (p x)}
  have hFree :
      IsFreeAmalgam
        (exactFreeCoverRootToLeft Source LeftSet RightSet)
        (exactFreeCoverRootToRight Source LeftSet RightSet)
        (inclusion Source LeftSet) (inclusion Source RightSet) :=
    native2019_positive_two_rest_source_free
      Source Old Support Core maps p hp i j hij
  let d : ProperFreeDecomposition Source := {
    Common := {x : U // x ∈ LeftSet ∩ RightSet}
    Left := LeftSet
    Right := RightSet
    common := Source.induce (LeftSet ∩ RightSet)
    left := Source.induce LeftSet
    right := Source.induce RightSet
    toLeft := exactFreeCoverRootToLeft Source LeftSet RightSet
    toRight := exactFreeCoverRootToRight Source LeftSet RightSet
    leftIn := inclusion Source LeftSet
    rightIn := inclusion Source RightSet
    free := hFree
    leftProper := by
      intro hSurj
      obtain ⟨x, hx⟩ := hActiveJ
      obtain ⟨y, hy⟩ := hSurj x
      change y.1 = x at hy
      exact (hy ▸ y.2) hx
    rightProper := by
      intro hSurj
      obtain ⟨x, hx⟩ := hActiveI
      obtain ⟨y, hy⟩ := hSurj x
      change y.1 = x at hy
      exact (hy ▸ y.2) hx
  }
  exact ⟨d⟩

end AllThoseRamseyClasses.Published
