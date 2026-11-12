import AllThoseRamseyClasses.Published.FunctionalWithParts2019IrreducibleRootRankStep

/-!
# Track C: U-irreducibility of the root hull suffices for original H gluing

The exact-source ambient-support gluing interface needs a closed
canonical K(H) boundary containing the weak common root.
Corrected (4b) supplies it whenever the ambient U-closure hull
of that root is U-irreducible; the original root itself may be
ordinary-reducible or nonclosed.

We prove the corresponding H-relative gluing, a generator-rank-j
small-side completion step, and the obstruction contrapositive.
Original weak carriers and whole OLD domain masks are unchanged.
No unconditional higher-rank increment and no implication from
the printed n-vertex local axiom are claimed.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {RootV LeftV RightV WholeV CandV : Type w}

/-- An irreducible ambient root hull is a canonical shared H-boundary,
even if its original weak root is reducible. -/
theorem genuinePartite2019_relativeCompletion_glue_rootHullUIrred
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hKIrr : ∀ {X : Type w}
      (D : RelStructure
        ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    (C : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) CandV)
    (hCClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    {Root : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) RootV}
    {Left : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) LeftV}
    {Right : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) RightV}
    {Whole : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) WholeV}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (eWhole : Embedding Whole C)
    (hL : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iL))
    (hR : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iR))
    (hRootHullUIrred : IsUIrreducible
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (UClosureHull
        ((L.withParts Parts).wholeMaskClosureRules Parts) C
        (Set.range (eWhole.comp (iL.comp sL)).toFun))))
    (hLeftHullComplete :
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce
          (UClosureHull
            ((L.withParts Parts).wholeMaskClosureRules Parts) C
            (Set.range (eWhole.comp iL).toFun))))
    (hRightHullComplete :
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce
          (UClosureHull
            ((L.withParts Parts).wholeMaskClosureRules Parts) C
            (Set.range (eWhole.comp iR).toFun)))) :
    HasGenuinePartiteTagged2019RelativeCompletion H Whole := by
  classical
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  let eLeft : Embedding Left C := eWhole.comp iL
  let eRight : Embedding Right C := eWhole.comp iR
  let eRoot : Embedding Root C := eWhole.comp (iL.comp sL)
  let SeedRoot : Set CandV := Set.range eRoot.toFun
  let SeedLeft : Set CandV := Set.range eLeft.toFun
  let SeedRight : Set CandV := Set.range eRight.toFun
  let Q : Set CandV := UClosureHull rules C SeedRoot
  let DL : Set CandV := UClosureHull rules C SeedLeft
  let DR : Set CandV := UClosureHull rules C SeedRight
  have hQClosed : IsUClosed rules (C.induce Q) :=
    hCClosed.induce_UClosureHull SeedRoot
  have hQK : canonicalGenuineTagged2019Class H (C.induce Q) :=
    hCovered Q hQClosed hRootHullUIrred
  have hSeedRootLeft : SeedRoot ⊆ SeedLeft := by
    intro z hz
    rcases hz with ⟨d, hd⟩
    refine ⟨sL d, ?_⟩
    exact hd
  have hSeedRootRight : SeedRoot ⊆ SeedRight := by
    intro z hz
    rcases hz with ⟨d, hd⟩
    refine ⟨sR d, ?_⟩
    calc
      eRight (sR d) = eRoot d := by
        have heq :
            iL (sL d) = iR (sR d) :=
          (hFree.overlap (sL d) (sR d)).mpr ⟨d, rfl, rfl⟩
        exact congrArg eWhole heq.symm
      _ = z := hd
  have hQL : Q ⊆ DL :=
    UClosureHull_mono rules C hSeedRootLeft
  have hQR : Q ⊆ DR :=
    UClosureHull_mono rules C hSeedRootRight
  have hRootIn (d : RootV) : eWhole (iL (sL d)) ∈ Q :=
    subset_UClosureHull rules C SeedRoot ⟨d, rfl⟩
  have hLeftIn (a : LeftV) : eWhole (iL a) ∈ DL :=
    subset_UClosureHull rules C SeedLeft ⟨a, rfl⟩
  have hRightIn (b : RightV) : eWhole (iR b) ∈ DR :=
    subset_UClosureHull rules C SeedRight ⟨b, rfl⟩
  exact genuinePartite2019_relativeCompletion_glue_over_ambient_supports
    H hStrong hKIrr C hFree eWhole hL hR
    Q DL DR hQL hQR hRootIn hLeftIn hRightIn
    hQK hLeftHullComplete hRightHullComplete


/-- Quantitative rank-j version. Side hulls can contain more than j vertices. -/
theorem genuinePartite2019_rankStep_of_rootHullUIrred
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hKIrr : ∀ {X : Type w}
      (D : RelStructure
        ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    (C : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) CandV)
    [Finite CandV]
    (hCClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (j : ℕ)
    (hRank : ∀ (T : Set CandV) [Fintype T],
      IsUClosed
        ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) →
      USize
        ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) ≤ j →
      HasGenuinePartiteTagged2019RelativeCompletion H (C.induce T))
    {Root : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) RootV}
    {Left : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) LeftV}
    {Right : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) RightV}
    {Whole : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) WholeV}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (eWhole : Embedding Whole C)
    (hL : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iL))
    (hR : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iR))
    [Finite LeftV] [Finite RightV]
    (hLeftSmall : Nat.card LeftV ≤ j)
    (hRightSmall : Nat.card RightV ≤ j)
    (hRootHullUIrred : IsUIrreducible
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (UClosureHull
        ((L.withParts Parts).wholeMaskClosureRules Parts) C
        (Set.range (eWhole.comp (iL.comp sL)).toFun)))) :
    HasGenuinePartiteTagged2019RelativeCompletion H Whole := by
  classical
  letI : Fintype CandV := Fintype.ofFinite CandV
  letI : Fintype LeftV := Fintype.ofFinite LeftV
  letI : Fintype RightV := Fintype.ofFinite RightV
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  let eLeft : Embedding Left C := eWhole.comp iL
  let eRight : Embedding Right C := eWhole.comp iR
  let SLeft : Finset CandV := Finset.univ.image eLeft.toFun
  let SRight : Finset CandV := Finset.univ.image eRight.toFun
  have hSLeft : (↑SLeft : Set CandV) = Set.range eLeft.toFun := by
    ext x
    simp [SLeft]
  have hSRight : (↑SRight : Set CandV) = Set.range eRight.toFun := by
    ext x
    simp [SRight]
  have hLeftCard : SLeft.card ≤ j := by
    calc
      SLeft.card ≤ (Finset.univ : Finset LeftV).card :=
        Finset.card_image_le
      _ = Fintype.card LeftV := Finset.card_univ
      _ = Nat.card LeftV := by rw [Nat.card_eq_fintype_card]
      _ ≤ j := hLeftSmall
  have hRightCard : SRight.card ≤ j := by
    calc
      SRight.card ≤ (Finset.univ : Finset RightV).card :=
        Finset.card_image_le
      _ = Fintype.card RightV := Finset.card_univ
      _ = Nat.card RightV := by rw [Nat.card_eq_fintype_card]
      _ ≤ j := hRightSmall
  have hLeftRank :
      USize rules
        (C.induce
          (UClosureHull rules C (Set.range eLeft.toFun))) ≤ j := by
    rw [← hSLeft]
    exact (USize_induce_UClosureHull_le rules C SLeft).trans hLeftCard
  have hRightRank :
      USize rules
        (C.induce
          (UClosureHull rules C (Set.range eRight.toFun))) ≤ j := by
    rw [← hSRight]
    exact (USize_induce_UClosureHull_le rules C SRight).trans hRightCard
  have hLeftHullClosed :
      IsUClosed rules
        (C.induce (UClosureHull rules C (Set.range eLeft.toFun))) :=
    hCClosed.induce_UClosureHull (Set.range eLeft.toFun)
  have hRightHullClosed :
      IsUClosed rules
        (C.induce (UClosureHull rules C (Set.range eRight.toFun))) :=
    hCClosed.induce_UClosureHull (Set.range eRight.toFun)
  have hLeftHullComplete :
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (UClosureHull rules C (Set.range eLeft.toFun))) :=
    hRank _ hLeftHullClosed hLeftRank
  have hRightHullComplete :
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (UClosureHull rules C (Set.range eRight.toFun))) :=
    hRank _ hRightHullClosed hRightRank
  exact genuinePartite2019_relativeCompletion_glue_rootHullUIrred
    H hStrong hKIrr C hCClosed hCovered
    hFree eWhole hL hR hRootHullUIrred
    hLeftHullComplete hRightHullComplete


/-- The ambient U-closure of the common root of every eligible
small relatively U-closed free cut of an uncompletable exact weak
test is necessarily U-reducible. Unlike the ordinary-reducible
root obstruction, this also excludes weak reducible roots whose
ambient U-closure happens to be U-irreducible. -/
theorem genuineTagged2019_badWeak_cut_rootHull_notUIrred
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hKIrr : ∀ {X : Type w}
      (Target : RelStructure
        ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H Target → Target.Irreducible)
    (C : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) CandV)
    [Finite CandV]
    (hCClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (j : ℕ)
    (hRank : ∀ (T : Set CandV) [Fintype T],
      IsUClosed
        ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) →
      USize
        ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) ≤ j →
      HasGenuinePartiteTagged2019RelativeCompletion H (C.induce T))
    (S : Finset CandV)
    (hBad : ¬ HasGenuinePartiteTagged2019RelativeCompletion
      H (C.induce (↑S : Set CandV)))
    (d : ProperFreeDecomposition (C.induce (↑S : Set CandV)))
    (hL : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑S : Set CandV)) (Set.range d.leftIn))
    (hR : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑S : Set CandV)) (Set.range d.rightIn))
    (hLeftSmall : Nat.card d.Left ≤ j)
    (hRightSmall : Nat.card d.Right ≤ j) :
    ¬ IsUIrreducible
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (UClosureHull
        ((L.withParts Parts).wholeMaskClosureRules Parts) C
        (Set.range
          ((inclusion C (↑S : Set CandV)).comp
            (d.leftIn.comp d.toLeft)).toFun))) := by
  intro hRootHullUIrred
  letI : Finite d.Left :=
    Finite.of_injective d.leftIn d.leftIn.injective
  letI : Finite d.Right :=
    Finite.of_injective d.rightIn d.rightIn.injective
  let eWhole : Embedding (C.induce (↑S : Set CandV)) C :=
    inclusion C (↑S : Set CandV)
  have hCompletion :
      HasGenuinePartiteTagged2019RelativeCompletion
        H (C.induce (↑S : Set CandV)) :=
    genuinePartite2019_rankStep_of_rootHullUIrred
      H hStrong hKIrr C hCClosed hCovered j hRank
      d.free eWhole hL hR hLeftSmall hRightSmall hRootHullUIrred
  exact hBad hCompletion

end AllThoseRamseyClasses.Published
