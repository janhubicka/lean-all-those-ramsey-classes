import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosureNativeWeakCutBoundary

/-!
# 2019 Lemma 2.30: genuine native copy/rest free cuts pull back POSITIVELY

The corrected 2019 Picture projection from a closed Ramsey witness
into a temporary native Hales--Jewett attachment need NOT be
globally injective. Thus one cannot treat an exact weak source
as literally embedded in the attachment.

But positivity alone suffices to pull back the attachment's
genuine copy/rest free RELATIONAL cover:

* the target's chosen old-copy vertices and its complementary
  rest cover every vertex and contain every relation tuple in
  at least one whole side;
* the inverse-image source vertex sets therefore form an
  actual free amalgam of the EXACT induced source sides;
* the source-side intersection is the literal preimage of the
  selected copy/rest overlap and is not replaced by a hull.

This proof is independent of U-closedness or semi-closedness of
the temporary attachment. It works with noninjective projections
and weak tested sources, as required by Definition 2.17(4c).

A full proper free cut requires both inverse-image sides to be
proper. The next rank argument also needs two old-picture maps
and compatible embeddings of a single closed A-boundary. Neither
condition is falsely derived here from the existence of a
relational free cover.

The first theorem is the general positive-cover pullback, following
the independently developed upstream draft of
ClosurePositiveFreeCoverPullback; the second directly verifies its
hypotheses on the TRUE native Attachment.attach constructors.

No strict rank increment or general corrected Theorem 2.18 is
asserted.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment

universe u v
variable {L : RelLanguage.{u}}

/-- Exact weak root embedding into the left induced side of any
source decomposition by two vertex sets. -/
def exactFreeCoverRootToLeft
    {U : Type v} (A : RelStructure L U)
    (S T : Set U) :
    Embedding (A.induce (S ∩ T)) (A.induce S) where
  toFun := fun x => ⟨x.1, x.2.1⟩
  injective := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : S => z.1) h
  map_rel_iff := fun _ _ => Iff.rfl

/-- Exact weak root embedding into the right side. -/
def exactFreeCoverRootToRight
    {U : Type v} (A : RelStructure L U)
    (S T : Set U) :
    Embedding (A.induce (S ∩ T)) (A.induce T) where
  toFun := fun x => ⟨x.1, x.2.2⟩
  injective := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : T => z.1) h
  map_rel_iff := fun _ _ => Iff.rfl

/-- ANY positive relational map pulls back an exact free target cover.
Neither source/target closedness nor injectivity/relational reflection
is needed. The vertex carriers stay EXACT inverse images. -/
theorem positive2019_pullback_exact_free_cover
    {U V : Type v}
    {A : RelStructure L U} {B : RelStructure L V}
    {f : U → V}
    (hf : A.IsHomomorphism B f)
    (S T : Set V)
    (hCover : ∀ y : V, y ∈ S ∨ y ∈ T)
    (hTuples : ∀ R (z : Fin (L.arity R) → V),
      B.rel R z →
        (∀ k, z k ∈ S) ∨ (∀ k, z k ∈ T)) :
    IsFreeAmalgam
      (exactFreeCoverRootToLeft A (f ⁻¹' S) (f ⁻¹' T))
      (exactFreeCoverRootToRight A (f ⁻¹' S) (f ⁻¹' T))
      (inclusion A (f ⁻¹' S))
      (inclusion A (f ⁻¹' T)) := by
  let SL : Set U := f ⁻¹' S
  let SR : Set U := f ⁻¹' T
  change IsFreeAmalgam
    (exactFreeCoverRootToLeft A SL SR)
    (exactFreeCoverRootToRight A SL SR)
    (inclusion A SL) (inclusion A SR)
  constructor
  · intro x
    rcases hCover (f x) with hs | ht
    · exact Or.inl ⟨⟨x, hs⟩, rfl⟩
    · exact Or.inr ⟨⟨x, ht⟩, rfl⟩
  · intro x y
    constructor
    · intro hxy
      have heq : x.1 = y.1 := hxy
      have hRight : f x.1 ∈ T := by
        rw [heq]
        exact y.2
      exact ⟨⟨x.1, x.2, hRight⟩,
        Subtype.ext rfl, Subtype.ext heq.symm⟩
    · rintro ⟨r, rfl, rfl⟩
      rfl
  · intro R z
    constructor
    · intro hz
      rcases hTuples R (f ∘ z) (hf R z hz) with hs | ht
      · exact Or.inl ⟨(fun k => ⟨z k, hs k⟩), hz, rfl⟩
      · exact Or.inr ⟨(fun k => ⟨z k, ht k⟩), hz, rfl⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact ha
      · exact hb

/-- For the REAL native simultaneous attachment and ANY old-copy
index i, pulling the literal copy/rest cover through ANY POSITIVE
source map produces an exact relational free amalgam of the
ORIGINAL source's induced inverse-image sides.

The temporary native attachment is allowed to be non-U-closed and
non-U-semi-closed. The projection is allowed to be noninjective.
No artificial closure hull or assumed partite picture is used. -/
theorem native2019_positive_source_copy_rest_free
    {U V W I : Type v}
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphism
      (attach Old Support Core maps) p)
    (i : I) :
    let Copy : Set (Vertex Support (W := W) (I := I)) :=
      {z | InCopy Old Support Core maps i z}
    let Rest : Set (Vertex Support (W := W) (I := I)) :=
      {z | ¬ OutsideAt (W := W) (I := I) Support i z}
    IsFreeAmalgam
      (exactFreeCoverRootToLeft Source (p ⁻¹' Copy) (p ⁻¹' Rest))
      (exactFreeCoverRootToRight Source (p ⁻¹' Copy) (p ⁻¹' Rest))
      (inclusion Source (p ⁻¹' Copy))
      (inclusion Source (p ⁻¹' Rest)) := by
  classical
  let Copy : Set (Vertex Support (W := W) (I := I)) :=
    {z | InCopy Old Support Core maps i z}
  let Rest : Set (Vertex Support (W := W) (I := I)) :=
    {z | ¬ OutsideAt (W := W) (I := I) Support i z}
  have hCover : ∀ z : Vertex Support (W := W) (I := I),
      z ∈ Copy ∨ z ∈ Rest := by
    intro z
    by_cases hz : OutsideAt (W := W) (I := I) Support i z
    · left
      obtain ⟨x, hx⟩ := hz
      exact ⟨x.1, hx.trans
        (copyMap_not_mem i x.1 x.2).symm⟩
    · exact Or.inr hz
  have hTuples :
      ∀ R (xs : Fin (L.arity R) →
        Vertex Support (W := W) (I := I)),
      (attach Old Support Core maps).rel R xs →
        (∀ k, xs k ∈ Copy) ∨
        (∀ k, xs k ∈ Rest) := by
    intro R xs hxs
    rcases hxs with ⟨ys, _, heq⟩ | ⟨j, ys, _, heq⟩
    · right
      intro k hout
      obtain ⟨x, hx⟩ := hout
      have hCore : xs k = Sum.inl (ys k) :=
        congrFun heq k
      rw [hx] at hCore
      cases hCore
    · by_cases hji : j = i
      · subst j
        left
        intro k
        exact ⟨ys k, congrFun heq k⟩
      · right
        intro k hout
        have hOutsideNot :
            ¬ OutsideAt (W := W) (I := I)
              Support i (copyMap Old Support Core maps j (ys k)) :=
          copyMap_not_outside_of_ne
            (B := Old) (S := Support) (D := Core) (f := maps)
            (i := i) j hji (ys k)
        have hk : xs k = copyMap Old Support Core maps j (ys k) :=
          congrFun heq k
        exact hOutsideNot (hk ▸ hout)
  exact positive2019_pullback_exact_free_cover
    hp Copy Rest hCover hTuples

/-- Specialize the concrete source cut to the proposed CORRECTED
2019 protected projection. Only POSITIVITY is used, so there is
no assumption that the little Picture's temporary native
attachment is closed or that the map is injective. -/
theorem native2019_corrected_source_copy_rest_free
    {rules : ClosureDescription L}
    {U V W I : Type v}
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : IsInducedClosedUHomomorphismEmbedding rules
      Source (attach Old Support Core maps) p)
    (i : I) :
    let Copy : Set (Vertex Support (W := W) (I := I)) :=
      {z | InCopy Old Support Core maps i z}
    let Rest : Set (Vertex Support (W := W) (I := I)) :=
      {z | ¬ OutsideAt (W := W) (I := I) Support i z}
    IsFreeAmalgam
      (exactFreeCoverRootToLeft Source (p ⁻¹' Copy) (p ⁻¹' Rest))
      (exactFreeCoverRootToRight Source (p ⁻¹' Copy) (p ⁻¹' Rest))
      (inclusion Source (p ⁻¹' Copy))
      (inclusion Source (p ⁻¹' Rest)) :=
  native2019_positive_source_copy_rest_free
    Source Old Support Core maps p hp.1 i


/-- If the original exact source has a vertex projecting to the
PRIVATE exterior of the chosen copy i, and another vertex projecting
OUTSIDE the entire chosen old-copy range, then the actual pulled-back
copy/rest free source cut is PROPER on both sides.

Neither the source map nor its restriction is required injective.
No relative U-closedness of the temporary native core or rest is
assumed, which would be false for nonclosed attaching supports. -/
theorem native2019_positive_source_copy_rest_proper
    {U V W I : Type v}
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphism
      (attach Old Support Core maps) p)
    (i : I)
    (hChosenPrivate : ∃ x : U,
      OutsideAt (W := W) (I := I) Support i (p x))
    (hBeyondChosenCopy : ∃ y : U,
      ¬ InCopy Old Support Core maps i (p y)) :
    Nonempty (ProperFreeDecomposition Source) := by
  classical
  let Copy : Set (Vertex Support (W := W) (I := I)) :=
    {z | InCopy Old Support Core maps i z}
  let Rest : Set (Vertex Support (W := W) (I := I)) :=
    {z | ¬ OutsideAt (W := W) (I := I) Support i z}
  let LeftSet : Set U := p ⁻¹' Copy
  let RightSet : Set U := p ⁻¹' Rest
  have hFree :
      IsFreeAmalgam
        (exactFreeCoverRootToLeft Source LeftSet RightSet)
        (exactFreeCoverRootToRight Source LeftSet RightSet)
        (inclusion Source LeftSet) (inclusion Source RightSet) :=
    native2019_positive_source_copy_rest_free
      Source Old Support Core maps p hp i
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
      obtain ⟨y, hy⟩ := hBeyondChosenCopy
      obtain ⟨x, hx⟩ := hSurj y
      change x.1 = y at hx
      exact hy (hx ▸ x.2)
    rightProper := by
      intro hSurj
      obtain ⟨y, hy⟩ := hChosenPrivate
      obtain ⟨x, hx⟩ := hSurj y
      change x.1 = y at hx
      exact (hx ▸ x.2) hy
  }
  exact ⟨d⟩

/-- If an exact weak source has at most j+1 vertices and its
POSITIVE projection meets both the chosen copy's private exterior
and the complement of that copy range, the TRUE native
copy/rest decomposition has TWO PROPER sides of at most j vertices.

This is an ABSOLUTE source vertex bound, not a claim about the
size of the closure of either projected side in the old picture.
The two ordinary side maps and their common A-boundary are
independent remaining obligations. -/
theorem native2019_positive_source_proper_cut_small_sides
    {U V W I : Type v}
    [Fintype U]
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphism
      (attach Old Support Core maps) p)
    (i : I) (j : ℕ)
    (hCard : Fintype.card U ≤ j + 1)
    (hChosenPrivate : ∃ x : U,
      OutsideAt (W := W) (I := I) Support i (p x))
    (hBeyondChosenCopy : ∃ y : U,
      ¬ InCopy Old Support Core maps i (p y)) :
    ∃ d : ProperFreeDecomposition Source,
      Nat.card d.Left ≤ j ∧ Nat.card d.Right ≤ j := by
  classical
  obtain ⟨d⟩ :=
    native2019_positive_source_copy_rest_proper
      Source Old Support Core maps p hp i
      hChosenPrivate hBeyondChosenCopy
  letI : Finite d.Left :=
    Finite.of_injective d.leftIn d.leftIn.injective
  letI : Finite d.Right :=
    Finite.of_injective d.rightIn d.rightIn.injective
  letI : Fintype d.Left := Fintype.ofFinite d.Left
  letI : Fintype d.Right := Fintype.ofFinite d.Right
  have hLessL : Fintype.card d.Left < Fintype.card U :=
    Fintype.card_lt_of_injective_not_surjective
      d.leftIn d.leftIn.injective d.leftProper
  have hLessR : Fintype.card d.Right < Fintype.card U :=
    Fintype.card_lt_of_injective_not_surjective
      d.rightIn d.rightIn.injective d.rightProper
  refine ⟨d, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card]
    omega
  · rw [Nat.card_eq_fintype_card]
    omega

end AllThoseRamseyClasses.Published
