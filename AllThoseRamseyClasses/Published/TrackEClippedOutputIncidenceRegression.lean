import AllThoseRamseyClasses.Published.TrackEActualStandardSystemSparseWitness
import PartiteConstruction.Functional.AmbientRelativeWeakFunctions

/-!
# Track E2 B3: a clipped multivalued fibre destroys native weak incidence

This is a *small verified primitive* for issue #967, not yet a
counterexample to the entire corrected 2019 tagged H-completion
predicate.  The latter additionally requires an actual tagged
IsInducedClosedUHomomorphismEmbedding.  That stronger premise must
be checked separately.

Take a unary set-valued function with F(0)={1,2}, then test only
the literal weak set S={0,1}.  A target has F(0)={2,3}, with vertex
3 of the same part as source vertex 1.  The full output PART masks
are equal, but the map on S sending 0↦0 and 1↦1 does not preserve
the surviving incidence 1∈F(0).

This is the exact semantic clause that must be provided by any
2019 OLD-complete-mask → native ambient-relative B3 transfer.
No closure hull of S is used. No original manuscript changes.
-/

namespace AllThoseRamseyClasses.Published.TrackEClippedOutputIncidenceRegression

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure

/-- One original binary relation and one unary set-valued function. -/
def toyLanguage : Language where
  RelSymbol := Unit
  FuncSymbol := Unit
  relArity := fun _ => 2
  funcArity := fun _ => 1

/-- A genuinely partial source, with a two-valued unary fibre at 0. -/
def sourcePartial : PartialSetStructure toyLanguage (Fin 3) where
  rel
    | (), xs => xs 0 ≠ xs 1
  func
    | (), xs =>
        if xs 0 = (0 : Fin 3) then
          some ({(1 : Fin 3), (2 : Fin 3)} : Set (Fin 3))
        else none

/-- A target whose output of part 1 is vertex 3 rather than vertex 1. -/
def targetPartial : PartialSetStructure toyLanguage (Fin 4) where
  rel
    | (), xs => xs 0 ≠ xs 1
  func
    | (), xs =>
        if xs 0 = (0 : Fin 4) then
          some ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4))
        else none

def sourceNative : Structure toyLanguage (Fin 3) :=
  sourcePartial.collapseDomain

def targetNative : Structure toyLanguage (Fin 4) :=
  targetPartial.collapseDomain

def sourcePart : Fin 3 → Fin 3 := id

def targetPart : Fin 4 → Fin 3 :=
  ![(0 : Fin 3), (1 : Fin 3), (2 : Fin 3), (1 : Fin 3)]

/-- Original exact weak test, not its generated function closure. -/
def testSet : Set (Fin 3) := {(0 : Fin 3), (1 : Fin 3)}

def x : testSet := ⟨0, by simp [testSet]⟩
def y : testSet := ⟨1, by simp [testSet]⟩

/-- The literal vertex map keeps both vertices of the exact weak test. -/
def f (a : testSet) : Fin 4 :=
  ⟨a.1.val, Nat.lt_trans a.1.isLt (by decide : 3 < 4)⟩

theorem f_x : f x = 0 := rfl
theorem f_y : f y = 1 := rfl

/-- Both original COMPLETE output fibres have the same set of PARTS,
despite their distinct actual part-1 output vertices. -/
theorem complete_output_part_masks_agree :
    sourcePart '' ({(1 : Fin 3), (2 : Fin 3)} : Set (Fin 3)) =
    targetPart '' ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4)) := by
  ext p
  fin_cases p <;> simp [sourcePart, targetPart]

/-- The source native weak restriction still remembers the surviving
output vertex 1 from the partially clipped fibre {1,2}. -/
theorem source_weak_has_surviving_output :
    y ∈ (sourceNative.weakInduce testSet).func ()
      (fun _ : Fin 1 => x) := by
  change (1 : Fin 3) ∈
    ({(1 : Fin 3), (2 : Fin 3)} : Set (Fin 3))
  simp

/-- The same-map target function does NOT contain vertex 1: its
part-1 output was moved to vertex 3 outside the test image. -/
theorem target_loses_surviving_output :
    f y ∉ targetNative.func () (fun _ : Fin 1 => f x) := by
  change (1 : Fin 4) ∉
    ({(2 : Fin 4), (3 : Fin 4)} : Set (Fin 4))
  simp

/-- A native ambient-relative weak map must preserve positive
incidences even when the other outputs are outside the exact test.
The proposed map fails already at this first native condition. -/
theorem not_native_ambient_relative_weakHom :
    ¬ IsAmbientRelativeWeakHomomorphism
      sourceNative testSet targetNative f := by
  intro h
  have hy := h.1.2 () (fun _ : Fin 1 => x) y
    source_weak_has_surviving_output
  exact target_loses_surviving_output hy

/-- Consequently the stronger native ambient-relative
homomorphism-embedding predicate also fails on the SAME map. -/
theorem not_native_ambient_relative_weakHE :
    ¬ IsAmbientRelativeWeakHE
      sourceNative testSet targetNative f := by
  intro h
  exact not_native_ambient_relative_weakHom h.1

end AllThoseRamseyClasses.Published.TrackEClippedOutputIncidenceRegression
