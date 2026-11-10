import AllThoseRamseyClasses.Published.TrackENativeFinalFibreTransversal
import PartiteConstruction.Functional.AmbientRelativeWeakFunctions
import PartiteConstruction.Structure.PartialSetFunctionsWholeWeak

/-!
# Track E2: native ambient-relative weak homomorphism from two EXACT map laws

The corrected finite-family E2 weak-locality notion requires:
(1) positive relational and surviving output INCIDENCE preservation
    on the literal clipped weak S, and
(2) exact equality of COMPLETE target fibres whenever the original
    ambient nonempty output set is wholly contained in S.

These are independent semantic requirements. This lemma assembles them
without changing the map f or enlarging S:

* a native weak homomorphism on the exact clipped source S, and
* the verified original-2019 source-defined partial homomorphism from
  the WHOLE-fibre weak genuine partial encoding on the SAME S.

A fully retained nonempty native fibre is a `some` value in the
whole-fibre partial source; the second condition therefore gives the
whole target fibre exactly. Partially clipped inputs are governed only
by the first condition, so no false total-domain reflection is assumed.

The first condition is precisely the positive graph-encoding task of
Track E2 #973; the second follows from genuine complete-output-mask
OLD local maps by the independently checked
`wholeWeakInduce_originalPartial_of_inducedOldHom` lemma.

This does NOT infer the protected-irreducible part of
`IsAmbientRelativeWeakHE`, assert that the current #924 whole-mask
witness carries a positive graph map, or construct the ordered E2
sparse Ramsey control.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- On the same native source, target, literal weak vertex set and map,
the native positive weak law and the genuine-partial WHOLE-fibre
source-defined law imply both clauses of ambient-relative weak
homomorphism. No output singleton assumption or domain reflection. -/
theorem ambientRelativeWeakHom_of_nativeWeak_and_wholePartial
    (A : Structure L V) (B : Structure L W)
    (S : Set V) (f : S → W)
    (hWeak : (A.weakInduce S).IsWeakHomomorphism B f)
    (hWhole : PartialSetStructure.IsOriginalPartialHomomorphism
      (PartialSetStructure.wholeWeakInduce A.toNonemptyPartial S)
      B.toNonemptyPartial f) :
    IsAmbientRelativeWeakHomomorphism A S B f := by
  classical
  refine ⟨hWeak, ?_⟩
  intro F xs hNonempty hAll
  let U : Set V := A.func F (Subtype.val ∘ xs)
  let U_S : Set S := {y : S | y.1 ∈ U}
  have hSome :
      A.toNonemptyPartial.func F (Subtype.val ∘ xs) = some U := by
    change (if U.Nonempty then some U else none) = some U
    exact if_pos hNonempty
  have hWholeVal :
      (PartialSetStructure.wholeWeakInduce A.toNonemptyPartial S).func
        F xs = some U_S := by
    change PartialSetStructure.wholeWeakValue S
      (A.toNonemptyPartial.func F (Subtype.val ∘ xs)) = some U_S
    rw [hSome]
    exact PartialSetStructure.wholeWeakValue_of_subset S U hAll
  have hTarget :
      B.toNonemptyPartial.func F (f ∘ xs) =
        some (Structure.imageSet f U_S) :=
    hWhole.2 F xs U_S hWholeVal
  have hTargetNonempty : (B.func F (f ∘ xs)).Nonempty := by
    by_contra hn
    have hNone :
        B.toNonemptyPartial.func F (f ∘ xs) = none := by
      change (if (B.func F (f ∘ xs)).Nonempty then
        some (B.func F (f ∘ xs)) else none) = none
      simp [hn]
    rw [hNone] at hTarget
    cases hTarget
  have hEqual :
      B.func F (f ∘ xs) = Structure.imageSet f U_S := by
    change (if (B.func F (f ∘ xs)).Nonempty then
      some (B.func F (f ∘ xs)) else none) =
      some (Structure.imageSet f U_S) at hTarget
    simpa [hTargetNonempty] using hTarget
  change Structure.imageSet f U_S = B.func F (f ∘ xs)
  exact hEqual.symm

end AllThoseRamseyClasses.Published
