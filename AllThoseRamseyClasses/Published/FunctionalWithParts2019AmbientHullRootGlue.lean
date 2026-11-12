import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeHGlue
import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosureIrreducibleHulls

/-!
# Track C: a shared ambient H-boundary for weak roots with irreducible hulls

The original weak source Whole stays on its EXACT vertex carrier.
We complete it by mapping its sides into larger, auxiliary induced
supports of one U-closed ambient candidate C. Those side supports
need not lie in the original source Whole.

Given a common closed canonical K(H) support Q in C containing the
image of the weak root, and two larger supports containing the images
of the sides and Q, the inclusions automatically form the compatible
projected maps required by the verified H-relative gluing theorem.
Thus no independent root-map compatibility oracle is necessary.

As a useful case, take Q to be the AMBIENT U-closure of an ORDINARY
irreducible weak root, and the two projected side sources to be
their ambient U-closure hulls. Corrected (4b) says Q is canonical
K(H), even if the original weak root itself is NOT U-closed.
The two side-hull H-completions are explicit premises.

This is a genuine additional positive case not covered by the simple
U-closed rank-one-root glue. It avoids replacing the tested original
weak source by any generated closure hull. It does NOT infer that the
side H-completions exist from a small-vertex local axiom; a separate
U-generating-rank bound is needed for that step.

Primitive partial functions remain genuine Option(Set) functions in
every canonical H target, with whole OLD domain masks retained.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {RootV LeftV RightV WholeV CandV : Type w}

/-- The verified projected-source genuine-H gluing theorem needs
no separate compatibility hypothesis when the projected sources
and their common closed K(H) boundary are induced structures on
NESTED vertex subsets of the SAME ambient candidate C.

Only the ORIGINAL free weak source Whole is completed; the larger
subsets are auxiliary target supports. -/
theorem genuinePartite2019_relativeCompletion_glue_over_ambient_supports
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hKIrr : ∀ {X : Type w}
      (D : RelStructure
        ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    (C : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) CandV)
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
    (BaseSet LeftSet RightSet : Set CandV)
    (hBaseLeft : BaseSet ⊆ LeftSet)
    (hBaseRight : BaseSet ⊆ RightSet)
    (hRootBase : ∀ d : RootV, eWhole (iL (sL d)) ∈ BaseSet)
    (hLeftSide : ∀ a : LeftV, eWhole (iL a) ∈ LeftSet)
    (hRightSide : ∀ b : RightV, eWhole (iR b) ∈ RightSet)
    (hBaseK : canonicalGenuineTagged2019Class H (C.induce BaseSet))
    (hLeftComplete :
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce LeftSet))
    (hRightComplete :
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce RightSet)) :
    HasGenuinePartiteTagged2019RelativeCompletion H Whole := by
  classical
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  letI : Finite BaseSet := hBaseK.1
  have hBaseClosed : IsUClosed rules (C.induce BaseSet) :=
    canonicalGenuineTagged2019Class_closed H (C.induce BaseSet) hBaseK
  let eLeft : Embedding Left C := eWhole.comp iL
  let eRight : Embedding Right C := eWhole.comp iR
  let left : Embedding Left (C.induce LeftSet) := {
    toFun := fun a => ⟨eLeft a, hLeftSide a⟩
    injective := by
      intro a b hab
      exact eLeft.injective (congrArg Subtype.val hab)
    map_rel_iff := by
      intro R xs
      exact eLeft.map_rel_iff R xs
  }
  let right : Embedding Right (C.induce RightSet) := {
    toFun := fun b => ⟨eRight b, hRightSide b⟩
    injective := by
      intro a b hab
      exact eRight.injective (congrArg Subtype.val hab)
    map_rel_iff := by
      intro R xs
      exact eRight.map_rel_iff R xs
  }
  let includeLeft : Embedding (C.induce BaseSet) (C.induce LeftSet) := {
    toFun := fun a => ⟨a.1, hBaseLeft a.2⟩
    injective := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun z : LeftSet => (z : CandV)) hab
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let includeRight : Embedding (C.induce BaseSet) (C.induce RightSet) := {
    toFun := fun a => ⟨a.1, hBaseRight a.2⟩
    injective := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun z : RightSet => (z : CandV)) hab
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let rootMap : RootV → BaseSet :=
    fun d => ⟨eWhole (iL (sL d)), hRootBase d⟩
  have hRootL (d : RootV) :
      left (sL d) = includeLeft (rootMap d) := by
    apply Subtype.ext
    rfl
  have hRootR (d : RootV) :
      right (sR d) = includeRight (rootMap d) := by
    apply Subtype.ext
    have hGlue :
        iL (sL d) = iR (sR d) :=
      (hFree.overlap (sL d) (sR d)).mpr ⟨d, rfl, rfl⟩
    exact congrArg eWhole hGlue.symm
  have hPLeft : IsInducedClosedUHomomorphismEmbedding
      rules Left (C.induce LeftSet) left.toFun :=
    IsClosedUHomomorphismEmbedding.toInducedClosed
      (left.isClosedUHomomorphismEmbedding rules)
  have hPRight : IsInducedClosedUHomomorphismEmbedding
      rules Right (C.induce RightSet) right.toFun :=
    IsClosedUHomomorphismEmbedding.toInducedClosed
      (right.isClosedUHomomorphismEmbedding rules)
  exact genuinePartite2019_relativeCompletion_glue_projected_sides
    H hStrong hKIrr hFree hL hR
    (C.induce BaseSet) hBaseK hBaseClosed
    (C.induce LeftSet) (C.induce RightSet)
    left.toFun right.toFun hPLeft hPRight
    rootMap includeLeft includeRight hRootL hRootR
    hLeftComplete hRightComplete

/-- If the common weak Root is ordinarily irreducible, its ambient
U-closure hull is U-closed and U-irreducible, hence canonical K(H)
by corrected (4b). The left/right ambient U-hulls both contain that
same canonical boundary. Explicit H-relative completions of those
side HULLS therefore glue to an H-relative completion of the
unchanged original weak free source Whole.

Neither Root nor either weak side is required intrinsically
U-closed. Side-hull completability remains a genuine hypothesis. -/
theorem genuinePartite2019_relativeCompletion_glue_irreducibleRoot_hull
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
    (hRootIrred : Root.Irreducible)
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
  have hSeedIrred : (C.induce SeedRoot).Irreducible :=
    hRootIrred.range_embedding eRoot
  have hQClosed : IsUClosed rules (C.induce Q) :=
    hCClosed.induce_UClosureHull SeedRoot
  have hQIrred : IsUIrreducible rules (C.induce Q) :=
    hCClosed.irreducibleSeed_hull_isUIrreducible
      SeedRoot hSeedIrred
  have hQK : canonicalGenuineTagged2019Class H (C.induce Q) :=
    hCovered Q hQClosed hQIrred
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

end AllThoseRamseyClasses.Published
