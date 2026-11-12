import AllThoseRamseyClasses.Published.TrackEOldMaskSplitAmbientHEIntegration
import AllThoseRamseyClasses.Lifts.FiniteFamilyAmbientRelativeLocality

/-!
# Track E2: exact split/mask certificates discharge finite-family native locality

The corrected E2 locality theorem is about the literal weak subsets
of a finite native shadow D, not their function closure. Merged Track
E2 #1003 gives the complete native IsAmbientRelativeWeakHE on the
same S and map f whenever:
1. there is a split-output-part ambient-relative weak HE, and
2. the same f preserves OLD active output-part domain masks.

This file packages those two independently meaningful local
certificates into a precise finite-family locality interface. Every
chosen completion target must itself be a FINITE genuine native
partite System whose ORIGINAL unsplit native structure avoids the
named finite forbidden family.

The first theorem supplies the exact verified
FiniteNamedAmbientRelativeWeakCompletions required by the finite
family E2 local-to-global theorem. The second derives actual native
forbidden-family avoidance once n bounds all named sources.

Both results are conditional: no sparse 2019 two-pass construction
of split/mask certificates is claimed; no extra tagged local
completion oracle is introduced; no implicit H-membership or
unproved strict mixed-root B-tree is smuggled into the conclusion.
No weak test is enlarged or replaced by a closure hull.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published

universe u v
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Every exact small weak subset S has a FINITE forbidden-free
partite completion target and ONE same-map pair of semantic
certificates: split native relative weak HE, plus positive OLD active
output-part domain-mask preservation. Both are required on the
literal S; the target is not allowed to vary between the two laws.

This is a named construction obligation, not a Ramsey conclusion. -/
def FiniteNamedSplitMaskRelativeWeakCompletions
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {V : Type} [Finite V]
    (A : FunctionalPartite.System L Parts V) (n : ℕ) : Prop :=
  ∀ (S : Set V), Nat.card S ≤ n →
    ∃ (W : Type) (_ : Finite W)
      (B : FunctionalPartite.System L Parts W),
      AvoidsFiniteNamedEHN Family B.toStructure ∧
      ∃ (f : S → W),
        IsAmbientRelativeWeakHE
          A.splitOutputParts.toStructure S
          B.splitOutputParts.toStructure f ∧
        (∀ (p : Language.FunctionInputPattern L)
          (q : Language.CompleteOutputParts Parts)
          (rootS : Fin p.rootSize → S),
          ((A.toStructure.toNonemptyPartial.wholeMaskPatternGraph A.part).induce S).rel
            (.inr (.inl (p, q))) rootS →
          (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part).rel
            (.inr (.inl (p, q))) (f ∘ rootS))

/-- The two SAME-MAP split/mask local certificates produce the actual
native ambient-relative weak completion predicate used by the
verified finite-family E2 theorem, at exactly the original cutoff n.
No larger carrier, generated hull, stronger ordinary EHN embedding,
or outside domain-reflection hypothesis is used. -/
theorem finiteNamedAmbientRelativeWeakCompletions_of_splitMask
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {V : Type} [Finite V]
    (A : FunctionalPartite.System L Parts V) (n : ℕ)
    (hLocal : FiniteNamedSplitMaskRelativeWeakCompletions
      Family A n) :
    FiniteNamedAmbientRelativeWeakCompletions
      Family A.toStructure n := by
  intro S hSize
  obtain ⟨W, hFinite, B, hAvoid, f, hSplit, hMask⟩ :=
    hLocal S hSize
  exact ⟨W, B.toStructure, hFinite, hAvoid, f,
    nativeAmbientRelativeWeakHE_of_splitHE_and_oldMaskMap
      A B S f hSplit hMask⟩

/-- If n bounds each forbidden native source, the precise split/mask
certificates on every exact weak S of size at most n imply the
actual finite-family EHN forbidden avoidance of A's original
unsplit native structure. The input still explicitly assumes the
local certificates; the hard sparse construction is separate. -/
theorem avoidsFiniteNamedEHN_of_splitMaskRelativeWeakCompletions
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {V : Type} [Finite V]
    (A : FunctionalPartite.System L Parts V) (n : ℕ)
    (hBound : ∀ i : Family.Index,
      Nat.card (Family.Carrier i) ≤ n)
    (hLocal : FiniteNamedSplitMaskRelativeWeakCompletions
      Family A n) :
    AvoidsFiniteNamedEHN Family A.toStructure := by
  exact avoidsFiniteNamedEHN_of_ambientRelativeWeakCompletions
    Family A.toStructure n hBound
    (finiteNamedAmbientRelativeWeakCompletions_of_splitMask
      Family A n hLocal)

end AllThoseRamseyClasses.Lifts
