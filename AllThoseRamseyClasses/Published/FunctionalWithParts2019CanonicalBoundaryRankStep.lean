import AllThoseRamseyClasses.Published.FunctionalWithParts2019CanonicalWeakRankCut
import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeHGlue

/-!
# Track C: exact conditional rank step and the noncanonical-boundary obstruction

At fixed j, the corrected-(4b) rank dichotomy proves:
each exact weak S of at most j+1 vertices is already H-completable,
or it has a proper free decomposition with relatively U-closed
side ranges and sides of at most j vertices.

The independently verified genuine H-relative gluing theorem shows
that such a free diagram is completable whenever the common root
is a member of K(H) and both sides have H-relative completions.
It uses ORIGINAL part-preserving strong amalgamation, and retains
persistent OLD domain masks and all protected closed U-tests.

This module puts the two ingredients together. Its genuinely
NONTRIVIAL remaining hypotheses are visible rather than smuggled in:

(1) all weak sources FULLY EMBEDDED into C with at most j vertices
    have actual H-relative completions (a strong inductive invariant);
(2) for each free decomposition produced in the hard branch, its
    common root lies in canonical K(H).

Under these assumptions the j -> j+1 weak-test step is valid.
Conversely, if a j+1-small weak S is NONcompletable but (1)
holds, the rank dichotomy exhibits a proper relative free cut
whose common root FAILS to belong to K(H). That is a precise
necessary obstruction to the naive induction.

Neither corrected (4b) nor maximal intrinsic U-size of a weak
test forces its common *weak* root to be U-closed. The Hales-Jewett
Picture history must supply a compatible closed K(H)-boundary
or otherwise repair the induction. A generated hull is NOT
substituted for the exact original S.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Given rank-j closed completion control, actual H-relative
completions for every smaller embedded weak source, and canonical
membership of the common root in any proper weak free decomposition,
the next weak-test cardinality layer is H-relatively completable.

The root-membership assumption is an EXPLICIT additional induction
invariant, not a consequence claimed from corrected (4b). -/
theorem genuineTagged2019_smallWeakCompletion_of_all_K_boundaries
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    [Finite V]
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hKIrr : ∀ {X : Type w}
      (Target : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H Target → Target.Irreducible)
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (j : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) →
      USize ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) ≤ j →
      HasGenuinePartiteTagged2019RelativeCompletion H (C.induce T))
    (hSmall : ∀ {X : Type w} [Finite X]
      (D : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      RelStructure.Embedding D C →
      Nat.card X ≤ j →
      HasGenuinePartiteTagged2019RelativeCompletion H D)
    (hRoots : ∀ (S : Finset V)
      (d : ProperFreeDecomposition (C.induce (↑S : Set V))),
      canonicalGenuineTagged2019Class H d.common)
    (S : Finset V) (hCard : S.card ≤ j + 1) :
    HasGenuinePartiteTagged2019RelativeCompletion
      H (C.induce (↑S : Set V)) := by
  classical
  rcases genuineTagged2019_weakSmall_complete_or_relativeFreeCut
      H C hClosed hCovered hKIrr j hRank S hCard with
      hDone | ⟨d, hRelL, hRelR, hSmallL, hSmallR⟩
  · exact hDone
  letI : Finite d.Left :=
    Finite.of_injective d.leftIn d.leftIn.injective
  letI : Finite d.Right :=
    Finite.of_injective d.rightIn d.rightIn.injective
  let inc : RelStructure.Embedding (C.induce (↑S : Set V)) C :=
    inclusion C (↑S : Set V)
  let eLeft : RelStructure.Embedding d.left C :=
    inc.comp d.leftIn
  let eRight : RelStructure.Embedding d.right C :=
    inc.comp d.rightIn
  have hLeft : HasGenuinePartiteTagged2019RelativeCompletion
      H d.left := hSmall d.left eLeft hSmallL
  have hRight : HasGenuinePartiteTagged2019RelativeCompletion
      H d.right := hSmall d.right eRight hSmallR
  exact genuinePartite2019_relativeCompletion_glue_over_H_root
    H hStrong hKIrr d.free hRelL hRelR
    (hRoots S d) hLeft hRight

/-- Necessary obstruction to the j+1 weak-test extension.
Provided rank-j closed control and completions of ALL smaller
embedded weak sources, a NONcompletable weak S must have a proper
relative free cut with a NON-K(H) common root.

The failure of canonical membership is the only conclusion:
the proof does not claim the root is intrinsically non-U-closed
under an arbitrary class H, nor that a replacement boundary
can always be built. -/
theorem genuineTagged2019_badWeakSmall_has_noncanonical_root
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    [Finite V]
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hKIrr : ∀ {X : Type w}
      (Target : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H Target → Target.Irreducible)
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (j : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) →
      USize ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) ≤ j →
      HasGenuinePartiteTagged2019RelativeCompletion H (C.induce T))
    (hSmall : ∀ {X : Type w} [Finite X]
      (D : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      RelStructure.Embedding D C →
      Nat.card X ≤ j →
      HasGenuinePartiteTagged2019RelativeCompletion H D)
    (S : Finset V) (hCard : S.card ≤ j + 1)
    (hBad : ¬ HasGenuinePartiteTagged2019RelativeCompletion
      H (C.induce (↑S : Set V))) :
    ∃ d : ProperFreeDecomposition (C.induce (↑S : Set V)),
      IsUSubstructure ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce (↑S : Set V)) (Set.range d.leftIn) ∧
      IsUSubstructure ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce (↑S : Set V)) (Set.range d.rightIn) ∧
      Nat.card d.Left ≤ j ∧ Nat.card d.Right ≤ j ∧
      ¬ canonicalGenuineTagged2019Class H d.common := by
  classical
  obtain ⟨d, hRelL, hRelR, hSmallL, hSmallR⟩ :=
    genuineTagged2019_badWeakSmall_has_relativeFreeCut
      H C hClosed hCovered hKIrr j hRank S hCard hBad
  letI : Finite d.Left :=
    Finite.of_injective d.leftIn d.leftIn.injective
  letI : Finite d.Right :=
    Finite.of_injective d.rightIn d.rightIn.injective
  let inc : RelStructure.Embedding (C.induce (↑S : Set V)) C :=
    inclusion C (↑S : Set V)
  let eLeft : RelStructure.Embedding d.left C :=
    inc.comp d.leftIn
  let eRight : RelStructure.Embedding d.right C :=
    inc.comp d.rightIn
  have hLeft : HasGenuinePartiteTagged2019RelativeCompletion H d.left :=
    hSmall d.left eLeft hSmallL
  have hRight : HasGenuinePartiteTagged2019RelativeCompletion H d.right :=
    hSmall d.right eRight hSmallR
  have hNotK : ¬ canonicalGenuineTagged2019Class H d.common := by
    intro hK
    exact hBad
      (genuinePartite2019_relativeCompletion_glue_over_H_root
        H hStrong hKIrr d.free hRelL hRelR hK hLeft hRight)
  exact ⟨d, hRelL, hRelR, hSmallL, hSmallR, hNotK⟩

end AllThoseRamseyClasses.Published
