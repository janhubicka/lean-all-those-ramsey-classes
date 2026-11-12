import AllThoseRamseyClasses.Published.FunctionalWithParts2019IrreducibleRootRankStep

/-!
# Track C: necessary ordinary-reducible boundary obstruction

This is a direct, test-carrier-exact contrapositive of the ambient-hull
rank step. It identifies the remaining structural obstruction without
claiming that a reducible cut can always be repaired.

Suppose corrected (4b) holds in a finite U-closed ambient C, H has
genuine original part-preserving strong amalgamation, and every
U-closed induced C-test of U-generator rank at most j has a genuine
H-relative completion. For a NONcompletable exact weak C-test S,
no free decomposition into two relatively U-closed proper sides
of size at most j can have an ORDINARY irreducible common root.

The statement quantifies over each such actual decomposition. It
does not assume that its root is U-closed or canonical K(H); it does
not substitute a generated hull for the original tested source, and
it does not turn the printed n-vertex local hypothesis into rank-j
completion control.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- A bad weak source cannot have even ONE small relatively U-closed
free cut with an ordinary-irreducible common root: the already
verified ambient-hull rank step would complete the same weak source. -/
theorem genuineTagged2019_badWeak_relativeFreeCut_root_reducible
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hKIrr : ∀ {X : Type w}
      (Target : RelStructure
        ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H Target → Target.Irreducible)
    (C : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    [Finite V]
    (hCClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (j : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed
        ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) →
      USize
        ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) ≤ j →
      HasGenuinePartiteTagged2019RelativeCompletion H (C.induce T))
    (S : Finset V)
    (hBad : ¬ HasGenuinePartiteTagged2019RelativeCompletion
      H (C.induce (↑S : Set V)))
    (d : ProperFreeDecomposition (C.induce (↑S : Set V)))
    (hL : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑S : Set V)) (Set.range d.leftIn))
    (hR : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑S : Set V)) (Set.range d.rightIn))
    (hLeftSmall : Nat.card d.Left ≤ j)
    (hRightSmall : Nat.card d.Right ≤ j) :
    ¬ d.common.Irreducible := by
  intro hRootIrred
  letI : Finite d.Left :=
    Finite.of_injective d.leftIn d.leftIn.injective
  letI : Finite d.Right :=
    Finite.of_injective d.rightIn d.rightIn.injective
  let eWhole : Embedding (C.induce (↑S : Set V)) C :=
    inclusion C (↑S : Set V)
  have hCompletion :
      HasGenuinePartiteTagged2019RelativeCompletion
        H (C.induce (↑S : Set V)) :=
    genuinePartite2019_rankStep_of_irreducibleRoot
      H hStrong hKIrr C hCClosed hCovered j hRank
      d.free eWhole hL hR hLeftSmall hRightSmall hRootIrred
  exact hBad hCompletion

end AllThoseRamseyClasses.Published
