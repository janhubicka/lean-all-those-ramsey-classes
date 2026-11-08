import AllThoseRamseyClasses.Published.FunctionalWithParts2019CanonicalKStrongAmalgamation
import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeKCompletion
import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosureBoundaryKGlue

/-!
# Track C: genuine H-relative completions glue over a common closed K-boundary

The verified relational 2019 completion-gluing theorem is already
available with exactly the RIGHT weak-source hypotheses:

* the source Whole is the full RELATIONAL free amalgam of Left and
  Right over Root;
* both side ranges inside Whole are RELATIVE U-substructures; the
  source sides themselves need NOT be intrinsically U-closed;
* Root is U-closed and belongs to the same canonical K(H) class;
* genuine H-relative completions of the Left and Right sources
  are given independently;
* H has the original finite PART-PRESERVING strong amalgamation
  property, and every canonical K(H) target is ordinarily irreducible.

These hypotheses ensure that the side completions can be strongly
amalgamated over ONE closed K-boundary, yielding a genuine H-valued
completion of the ENTIRE exact weak source. They do not require
source-closedness, a fixed B covering every test, or new source points.

The conclusion follows by interpreting each given H-relative
completion as a corrected induced-closed K-completion, using the
verified equivalence between the induced-closed and abstract
closed-test completion interfaces, invoking the closed-boundary
gluing theorem, and decoding the resulting K-completion back into
the original genuine partial Option(Set) H-target language.

This resolves the GLUING step **provided** the structural boundary
and independently completable side tests are available. It does not
establish the generator-rank budgets which produce those inputs from
the actual Hales-Jewett Picture history; no arbitrary minimum weak
generating-set completion is extended to its closed hull.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {HRoot ESide FSide VWhole : Type w}
variable {Root : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) HRoot}
variable {Left : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) ESide}
variable {Right : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) FSide}
variable {Whole : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) VWhole}
variable {sL : RelStructure.Embedding Root Left}
variable {sR : RelStructure.Embedding Root Right}
variable {iL : RelStructure.Embedding Left Whole}
variable {iR : RelStructure.Embedding Right Whole}

/-- Relative H-completability of both weak sides glues along an
ACTUAL common closed canonical H-root. It is crucial that the side
ranges are relatively U-closed in Whole; otherwise a mixed closure
tuple could break protection of a U-closed irreducible test.

No global U-closedness of Whole or of Left/Right is assumed. -/
theorem genuineTagged2019_relativeCompletion_glue_over_closed_H_root
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hKIrred : ∀ {X : Type w}
      (D : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    [Finite HRoot]
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hRelL :
      IsUSubstructure
        ((L.withParts Parts).wholeMaskClosureRules Parts)
        Whole (Set.range iL))
    (hRelR :
      IsUSubstructure
        ((L.withParts Parts).wholeMaskClosureRules Parts)
        Whole (Set.range iR))
    (hRootClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Root)
    (hRootK : canonicalGenuineTagged2019Class H Root)
    (hLeft : HasGenuinePartiteTagged2019RelativeCompletion H Left)
    (hRight : HasGenuinePartiteTagged2019RelativeCompletion H Right) :
    HasGenuinePartiteTagged2019RelativeCompletion H Whole := by
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  let K := canonicalGenuineTagged2019Class H
  have hKStrong : HasFiniteStrongAmalgamation K :=
    canonicalGenuineTagged2019Class_strongAmalgamation H hStrong
  have hLeftInduced : HasInducedClosedUKCompletion K rules Left :=
    (canonicalGenuineTagged2019_KCompletion_iff_relative H Left).mpr hLeft
  have hRightInduced : HasInducedClosedUKCompletion K rules Right :=
    (canonicalGenuineTagged2019_KCompletion_iff_relative H Right).mpr hRight
  have hLeftAbstract : HasClosedUKCompletion K rules Left :=
    inducedClosedKCompletion_iff_abstract_2019.mp hLeftInduced
  have hRightAbstract : HasClosedUKCompletion K rules Right :=
    inducedClosedKCompletion_iff_abstract_2019.mp hRightInduced
  have hWholeAbstract : HasClosedUKCompletion K rules Whole :=
    HasClosedUKCompletion.glue_over_closed_K_root_relative
      rules hKStrong hKIrred hFree hRelL hRelR
      hRootClosed hRootK hLeftAbstract hRightAbstract
  have hWholeInduced : HasInducedClosedUKCompletion K rules Whole :=
    inducedClosedKCompletion_iff_abstract_2019.mpr hWholeAbstract
  exact (canonicalGenuineTagged2019_KCompletion_iff_relative
    H Whole).mp hWholeInduced

/-- Contrapositive of the fully functional H-relative bridge:
under a fixed closed canonical H-boundary, if the exact free source
has NO H-relative completion, then at least one side has no
H-relative completion. This isolates the remaining rank increment:
one must prove an actual side has lower rank, not only smaller
vertex cardinality of some unrelated weak carrier. -/
theorem genuineTagged2019_bad_side_of_bad_free_relative
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hKIrred : ∀ {X : Type w}
      (D : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    [Finite HRoot]
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hRelL :
      IsUSubstructure
        ((L.withParts Parts).wholeMaskClosureRules Parts)
        Whole (Set.range iL))
    (hRelR :
      IsUSubstructure
        ((L.withParts Parts).wholeMaskClosureRules Parts)
        Whole (Set.range iR))
    (hRootClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Root)
    (hRootK : canonicalGenuineTagged2019Class H Root)
    (hBad : ¬ HasGenuinePartiteTagged2019RelativeCompletion H Whole) :
    (¬ HasGenuinePartiteTagged2019RelativeCompletion H Left) ∨
      (¬ HasGenuinePartiteTagged2019RelativeCompletion H Right) := by
  by_cases hLeft : HasGenuinePartiteTagged2019RelativeCompletion H Left
  · right
    intro hRight
    exact hBad (genuineTagged2019_relativeCompletion_glue_over_closed_H_root
      H hStrong hKIrred hFree hRelL hRelR
      hRootClosed hRootK hLeft hRight)
  · exact Or.inl hLeft

end AllThoseRamseyClasses.Published
