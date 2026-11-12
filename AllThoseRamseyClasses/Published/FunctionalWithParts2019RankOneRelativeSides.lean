import AllThoseRamseyClasses.Published.FunctionalWithParts2019RankOneRootGlue
import PartiteConstruction.Ramsey.ClosureFreeAmalgamRelativeRoot

/-!
# Track C: rank-one relative H-completion gluing needs no root-closedness premise

The verified partite-construction common-root theorem identifies the
original Root as U-closed whenever the Left side is U-closed and the
Right side has relatively U-closed image in the free source, even if
the Right side and Whole are not intrinsically U-closed.

Combining that result with the checked original genuine Option(Set)
partial-function H-completion gluing theorem for U-closed roots of
USize at most one gives a relative source theorem whose sole
root-specific input is the generating rank bound.

Two symmetric side variants and the both-closed free-amalgam variant
are stated explicitly. These retain the EXACT original weak Whole
carrier, its source-defined OLD domain masks, the corrected (4b)
coverage condition, and a single ambient candidate.

The theorem does not construct side H-completions, assume that an
arbitrary higher-rank reducible root lies in canonical K(H), or infer
the literal printed intrinsic local class axiom from a corrected
ambient-relative one.

The dependency pin in this PR is the exact verified partite-construction
merge commit for the relative common-root theorem (PR #596).
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {RootV LeftV RightV WholeV CandV : Type w}

/-- Original genuine H-valued completions of the sides of a free
weak source glue when Left is U-closed, both side images are relatively
U-closed in Whole, and the original common root is at most
one-generated. No U-closedness of Whole, Right, or Root is assumed. -/
theorem genuinePartite2019_relativeCompletion_glue_rankOne_leftClosed
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (hKIrr : ∀ {X : Type w}
      (D : RelStructure
        ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    (Candidate : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) CandV)
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) Candidate)
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
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (eWhole : Embedding Whole Candidate)
    (hL : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iL))
    (hR : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iR))
    (hLeftClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Left)
    [Fintype RootV]
    (hRank : USize
      ((L.withParts Parts).wholeMaskClosureRules Parts) Root ≤ 1)
    (hLeft : HasGenuinePartiteTagged2019RelativeCompletion H Left)
    (hRight : HasGenuinePartiteTagged2019RelativeCompletion H Right) :
    HasGenuinePartiteTagged2019RelativeCompletion H Whole := by
  have hRootClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Root :=
    hSrc.root_isUClosed_of_left_closed_right_relative hLeftClosed hR
  exact genuinePartite2019_relativeCompletion_glue_over_rankOne_root
    H hStrong hIso hKIrr Candidate hCovered
    hSrc eWhole hL hR hRootClosed hRank hLeft hRight

/-- Symmetric form: Right is U-closed and Left is merely relatively
U-closed in the whole. No Root or Whole closedness is assumed. -/
theorem genuinePartite2019_relativeCompletion_glue_rankOne_rightClosed
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (hKIrr : ∀ {X : Type w}
      (D : RelStructure
        ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    (Candidate : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) CandV)
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) Candidate)
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
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (eWhole : Embedding Whole Candidate)
    (hL : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iL))
    (hR : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iR))
    (hRightClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Right)
    [Fintype RootV]
    (hRank : USize
      ((L.withParts Parts).wholeMaskClosureRules Parts) Root ≤ 1)
    (hLeft : HasGenuinePartiteTagged2019RelativeCompletion H Left)
    (hRight : HasGenuinePartiteTagged2019RelativeCompletion H Right) :
    HasGenuinePartiteTagged2019RelativeCompletion H Whole := by
  have hRootClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Root :=
    hSrc.root_isUClosed_of_right_closed_left_relative hRightClosed hL
  exact genuinePartite2019_relativeCompletion_glue_over_rankOne_root
    H hStrong hIso hKIrr Candidate hCovered
    hSrc eWhole hL hR hRootClosed hRank hLeft hRight

/-- Fully closed special case: closedness of Whole and both sides
supplies all root and relative-range conditions needed for rank-one
H-completion gluing. The remaining original root input is USize<=1. -/
theorem genuinePartite2019_relativeCompletion_glue_rankOne_allClosed
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (hKIrr : ∀ {X : Type w}
      (D : RelStructure
        ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    (Candidate : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) CandV)
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) Candidate)
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
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (eWhole : Embedding Whole Candidate)
    (hWholeClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Whole)
    (hLeftClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Left)
    (hRightClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Right)
    [Fintype RootV]
    (hRank : USize
      ((L.withParts Parts).wholeMaskClosureRules Parts) Root ≤ 1)
    (hLeft : HasGenuinePartiteTagged2019RelativeCompletion H Left)
    (hRight : HasGenuinePartiteTagged2019RelativeCompletion H Right) :
    HasGenuinePartiteTagged2019RelativeCompletion H Whole := by
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  have hL : IsUSubstructure rules Whole (Set.range iL) :=
    iL.range_isUSubstructure hLeftClosed hWholeClosed
  have hR : IsUSubstructure rules Whole (Set.range iR) :=
    iR.range_isUSubstructure hRightClosed hWholeClosed
  exact genuinePartite2019_relativeCompletion_glue_rankOne_leftClosed
    H hStrong hIso hKIrr Candidate hCovered
    hSrc eWhole hL hR hLeftClosed hRank hLeft hRight

/-- Direct formulation of the relative rank-one gluing theorem
under the ambient class hypotheses K(H) subset R and R irreducible. -/
theorem genuinePartite2019_relativeCompletion_glue_rankOne_leftClosed_of_ambient
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (R : StructureClass
      (L := (L.withParts Parts).wholeMaskTagLanguage Parts))
    (hRIrred : ∀ {X : Type w}
      (D : RelStructure
        ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      R D → D.Irreducible)
    (hSub : ∀ {X : Type w}
      (D : RelStructure
        ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H D → R D)
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (Candidate : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) CandV)
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) Candidate)
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
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (eWhole : Embedding Whole Candidate)
    (hL : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iL))
    (hR : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iR))
    (hLeftClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Left)
    [Fintype RootV]
    (hRank : USize
      ((L.withParts Parts).wholeMaskClosureRules Parts) Root ≤ 1)
    (hLeft : HasGenuinePartiteTagged2019RelativeCompletion H Left)
    (hRight : HasGenuinePartiteTagged2019RelativeCompletion H Right) :
    HasGenuinePartiteTagged2019RelativeCompletion H Whole :=
  genuinePartite2019_relativeCompletion_glue_rankOne_leftClosed
    H hStrong hIso (fun D hK => hRIrred D (hSub D hK))
    Candidate hCovered hSrc eWhole hL hR hLeftClosed hRank
    hLeft hRight

end AllThoseRamseyClasses.Published
