import AllThoseRamseyClasses.Published.FunctionalWithParts2019CanonicalKStrongAmalgamation
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CanonicalKIso
import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeKCompletion
import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosureRelativeMapGlue

/-!
# Track C: conditional gluing of original H-valued relative weak completions

The corrected 2019 source is a tagged OLD/U relational structure,
while completion targets must be actual finite part-labelled genuine
Option(Set) members of the ORIGINAL H class.

The existing verified relational gluing theorem works for a source
free amalgam whose two side ranges are relatively U-closed. It can
combine *independently chosen* side completions, provided the side
maps factor through projected sources DL and DR containing the SAME
canonical U-closed K(H) boundary Q, with compatible root maps.

This file specializes that theorem to canonical genuinely partial
H targets. The resulting completion of the original free source Whole
has an actual H target and an induced-closed U-homomorphism-embedding
preserving all closed U-irreducible tests. Undefined and defined-empty
function values remain distinguished by the canonical tagged encoding.

This does NOT derive the shared closed boundary Q, the projected
compatible maps or relative side closedness from arbitrary intrinsic
weak completions. Strong amalgamation of H by itself does not supply
these extra source-side compatibility hypotheses. No weak carrier is
silently replaced by its generated hull.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {RootV LeftV RightV WholeV BoundaryV DLv DRv : Type w}

private abbrev taggedLanguage (L : Language.{u}) (Parts : Type v) [Fintype Parts] :=
  ((L.withParts Parts).wholeMaskTagLanguage Parts)

-- The target K(H) remains the exact canonical image of original
-- part-preserving partial-function structures, not an abstract K.

theorem genuinePartite2019_relativeCompletion_glue_projected_sides
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hKIrr : ∀ {X : Type w}
      (D : RelStructure (taggedLanguage L Parts) X),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    {Root : RelStructure (taggedLanguage L Parts) RootV}
    {Left : RelStructure (taggedLanguage L Parts) LeftV}
    {Right : RelStructure (taggedLanguage L Parts) RightV}
    {Whole : RelStructure (taggedLanguage L Parts) WholeV}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hL : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iL))
    (hR : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iR))
    [Finite BoundaryV]
    (Q : RelStructure (taggedLanguage L Parts) BoundaryV)
    (hQK : canonicalGenuineTagged2019Class H Q)
    (hQClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Q)
    (DL : RelStructure (taggedLanguage L Parts) DLv)
    (DR : RelStructure (taggedLanguage L Parts) DRv)
    (pL : LeftV → DLv) (pR : RightV → DRv)
    (hpL : IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Left DL pL)
    (hpR : IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Right DR pR)
    (q : RootV → BoundaryV)
    (rL : Embedding Q DL) (rR : Embedding Q DR)
    (hRootL : ∀ d, pL (sL d) = rL (q d))
    (hRootR : ∀ d, pR (sR d) = rR (q d))
    (hDL : HasGenuinePartiteTagged2019RelativeCompletion H DL)
    (hDR : HasGenuinePartiteTagged2019RelativeCompletion H DR) :
    HasGenuinePartiteTagged2019RelativeCompletion H Whole := by
  classical
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  have hStrongK :
      HasFiniteStrongAmalgamation (canonicalGenuineTagged2019Class H) :=
    canonicalGenuineTagged2019Class_strongAmalgamation H hStrong
  have hLeftInduced :
      HasInducedClosedUKCompletion
        (canonicalGenuineTagged2019Class H) rules DL :=
    (canonicalGenuineTagged2019_KCompletion_iff_relative H DL).mpr hDL
  have hRightInduced :
      HasInducedClosedUKCompletion
        (canonicalGenuineTagged2019Class H) rules DR :=
    (canonicalGenuineTagged2019_KCompletion_iff_relative H DR).mpr hDR
  have hLeftClosed :
      HasClosedUKCompletion
        (canonicalGenuineTagged2019Class H) rules DL :=
    (inducedClosedKCompletion_iff_abstract_2019).mp hLeftInduced
  have hRightClosed :
      HasClosedUKCompletion
        (canonicalGenuineTagged2019Class H) rules DR :=
    (inducedClosedKCompletion_iff_abstract_2019).mp hRightInduced
  have hWholeClosed :
      HasClosedUKCompletion
        (canonicalGenuineTagged2019Class H) rules Whole :=
    HasClosedUKCompletion.of_independent_projected_completions_relative
      rules hStrongK hKIrr hSrc hL hR
      Q hQK hQClosed DL DR pL pR
      (IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hpL)
      (IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hpR)
      q rL rR hRootL hRootR hLeftClosed hRightClosed
  have hWholeInduced :
      HasInducedClosedUKCompletion
        (canonicalGenuineTagged2019Class H) rules Whole :=
    (inducedClosedKCompletion_iff_abstract_2019).mpr hWholeClosed
  exact (canonicalGenuineTagged2019_KCompletion_iff_relative H Whole).mp
    hWholeInduced

/-- Original theorem-level ambient assumptions supply exactly the
irreducibility of canonical K(H)-targets needed by the gluing theorem.
The remaining compatible boundary/projected-map hypotheses are NOT
eliminated by this specialization. -/
theorem genuinePartite2019_relativeCompletion_glue_of_ambient
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (R : StructureClass (L := taggedLanguage L Parts))
    (hRIrred : ∀ {X : Type w}
      (D : RelStructure (taggedLanguage L Parts) X),
      R D → D.Irreducible)
    (hSub : ∀ {X : Type w}
      (D : RelStructure (taggedLanguage L Parts) X),
      canonicalGenuineTagged2019Class H D → R D)
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    {Root : RelStructure (taggedLanguage L Parts) RootV}
    {Left : RelStructure (taggedLanguage L Parts) LeftV}
    {Right : RelStructure (taggedLanguage L Parts) RightV}
    {Whole : RelStructure (taggedLanguage L Parts) WholeV}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hL : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iL))
    (hR : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iR))
    [Finite BoundaryV]
    (Q : RelStructure (taggedLanguage L Parts) BoundaryV)
    (hQK : canonicalGenuineTagged2019Class H Q)
    (hQClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Q)
    (DL : RelStructure (taggedLanguage L Parts) DLv)
    (DR : RelStructure (taggedLanguage L Parts) DRv)
    (pL : LeftV → DLv) (pR : RightV → DRv)
    (hpL : IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Left DL pL)
    (hpR : IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Right DR pR)
    (q : RootV → BoundaryV)
    (rL : Embedding Q DL) (rR : Embedding Q DR)
    (hRootL : ∀ d, pL (sL d) = rL (q d))
    (hRootR : ∀ d, pR (sR d) = rR (q d))
    (hDL : HasGenuinePartiteTagged2019RelativeCompletion H DL)
    (hDR : HasGenuinePartiteTagged2019RelativeCompletion H DR) :
    HasGenuinePartiteTagged2019RelativeCompletion H Whole :=
  genuinePartite2019_relativeCompletion_glue_projected_sides
    H hStrong (fun D hK => hRIrred D (hSub D hK))
    hSrc hL hR Q hQK hQClosed
    DL DR pL pR hpL hpR q rL rR
    hRootL hRootR hDL hDR


/-- Special case with no abstract projected boundary: if the common source
root is already a canonical K(H)-member, two genuine H-relative completions
of the two actual source sides automatically glue, with no separately
chosen Q, DL, DR or root comparison maps.

The common root's finite carrier and U-closedness follow from its
canonical H-membership. The inclusions sL,sR are full embeddings, so
the protected root test is automatically compatible across the two
side completions. Relatively closed source side ranges are still
essential and are stated explicitly. -/
theorem genuinePartite2019_relativeCompletion_glue_over_H_root
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hKIrr : ∀ {X : Type w}
      (D : RelStructure (taggedLanguage L Parts) X),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    {Root : RelStructure (taggedLanguage L Parts) RootV}
    {Left : RelStructure (taggedLanguage L Parts) LeftV}
    {Right : RelStructure (taggedLanguage L Parts) RightV}
    {Whole : RelStructure (taggedLanguage L Parts) WholeV}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hSrc : IsFreeAmalgam sL sR iL iR)
    (hL : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iL))
    (hR : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iR))
    (hRootK : canonicalGenuineTagged2019Class H Root)
    (hLeft : HasGenuinePartiteTagged2019RelativeCompletion H Left)
    (hRight : HasGenuinePartiteTagged2019RelativeCompletion H Right) :
    HasGenuinePartiteTagged2019RelativeCompletion H Whole := by
  classical
  letI : Finite RootV := hRootK.1
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  have hRootClosed : IsUClosed rules Root :=
    canonicalGenuineTagged2019Class_closed H Root hRootK
  have hIdL : IsInducedClosedUHomomorphismEmbedding
      rules Left Left (_root_.id : LeftV → LeftV) :=
    IsClosedUHomomorphismEmbedding.toInducedClosed
      ((Embedding.id Left).isClosedUHomomorphismEmbedding rules)
  have hIdR : IsInducedClosedUHomomorphismEmbedding
      rules Right Right (_root_.id : RightV → RightV) :=
    IsClosedUHomomorphismEmbedding.toInducedClosed
      ((Embedding.id Right).isClosedUHomomorphismEmbedding rules)
  exact genuinePartite2019_relativeCompletion_glue_projected_sides
    H hStrong hKIrr hSrc hL hR
    Root hRootK hRootClosed
    Left Right
    (_root_.id : LeftV → LeftV)
    (_root_.id : RightV → RightV)
    hIdL hIdR
    (_root_.id : RootV → RootV) sL sR
    (by intro d; rfl) (by intro d; rfl)
    hLeft hRight



/-- Corrected (4b) yields a canonical H-root automatically when the
common root embeds as a genuinely U-closed U-irreducible test in the
ambient candidate C and the original H class is isomorphism-closed.
The source's entire free-amalgam weak test itself need not be U-closed.

This is the exact favourable mixed case: a protected irreducible
boundary can be reused as the common canonical H-base for strong
amalgamation. The residual obstruction is a *reducible* boundary with
no such protected root membership, not the gluing operation itself. -/
theorem genuinePartite2019_relativeCompletion_glue_over_protected_root
    {CandV : Type w}
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (hKIrr : ∀ {X : Type w}
      (D : RelStructure (taggedLanguage L Parts) X),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    (Candidate : RelStructure (taggedLanguage L Parts) CandV)
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) Candidate)
    {Root : RelStructure (taggedLanguage L Parts) RootV}
    {Left : RelStructure (taggedLanguage L Parts) LeftV}
    {Right : RelStructure (taggedLanguage L Parts) RightV}
    {Whole : RelStructure (taggedLanguage L Parts) WholeV}
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
    (hRootClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Root)
    (hRootIrred : IsUIrreducible
      ((L.withParts Parts).wholeMaskClosureRules Parts) Root)
    (hLeft : HasGenuinePartiteTagged2019RelativeCompletion H Left)
    (hRight : HasGenuinePartiteTagged2019RelativeCompletion H Right) :
    HasGenuinePartiteTagged2019RelativeCompletion H Whole := by
  let eRoot : Embedding Root Candidate :=
    eWhole.comp (iL.comp sL)
  have hKiso : IsomorphismClosed2019
      (canonicalGenuineTagged2019Class H) :=
    canonicalGenuineTagged2019Class_isomorphismClosed H hIso
  have hCoverAbstract :
      ClosedUIrreduciblesIn (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) Candidate :=
    correctedInducedCoverage_toAbstract_2019 hKiso hCovered
  have hRootK : canonicalGenuineTagged2019Class H Root :=
    hCoverAbstract Root hRootClosed hRootIrred eRoot
  exact genuinePartite2019_relativeCompletion_glue_over_H_root
    H hStrong hKIrr hSrc hL hR hRootK hLeft hRight


end AllThoseRamseyClasses.Published
