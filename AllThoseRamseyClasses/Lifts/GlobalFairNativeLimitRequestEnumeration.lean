import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitFiniteCover
import Mathlib.Logic.Encodable.Basic

/-!
# Track F: an exhaustive optional enumeration and diagonal request schedule

The actual decoded native fair limit has a COUNTABLE carrier,
as already proved in the merged finite FULL stage-cover module.
The back-and-forth stage recursion needs a schedule that
eventually requests every vertex on both source and target.

Construct it using a noncanonical Encodable instance for the
countable limit carrier. At each natural number n, decode n;
if no vertex decodes, request the empty list, otherwise request
the singleton diagonal pair (x,x). Every limit vertex x occurs
at its own code.

Unlike a surjection ℕ→M, this works even if M is EMPTY:
a list-valued schedule may then be constantly empty. No
Inhabited/Nonempty assumption on the fair limit is needed.
The selection of Encodable is noncomputable, and introduces
no mathematical axiom beyond standard classical choice.

This is only an enumeration certificate, not a constructed
infinite automorphism. Still conditional on the original
finite Fraïssé input, including unresolved global shadow
avoidance in the general reducible forbidden-source case.
The numbered manuscript remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The actual countable limit carrier has an exhaustive
schedule of finite source/target vertex requests: EVERY
vertex occurs as a diagonal pair in some scheduled list.

The theorem does not presume that the limit has a vertex.
Consequently it works uniformly even for an empty limit. -/
theorem globalOriginalActualFairNativeLimit_diagonalSchedule_exists
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F) :
    ∃ schedule : ℕ →
        List
          ((GlobalOriginalTraceFirstOrderDirectLimit F hInput
              (globalOriginalRepresentativePrefix F hInput)
              (globalOriginalExtensionDiagramPrefix F hInput)) ×
           (GlobalOriginalTraceFirstOrderDirectLimit F hInput
              (globalOriginalRepresentativePrefix F hInput)
              (globalOriginalExtensionDiagramPrefix F hInput))),
      ∀ x : GlobalOriginalTraceFirstOrderDirectLimit F hInput
        (globalOriginalRepresentativePrefix F hInput)
        (globalOriginalExtensionDiagramPrefix F hInput),
        ∃ n : ℕ, (x, x) ∈ schedule n := by
  classical
  let M := GlobalOriginalTraceFirstOrderDirectLimit F hInput
    (globalOriginalRepresentativePrefix F hInput)
    (globalOriginalExtensionDiagramPrefix F hInput)
  letI : Countable M :=
    globalOriginalActualFairNativeLimit_countable F hInput
  letI : Encodable M := Encodable.ofCountable M
  let schedule : ℕ → List (M × M) := fun n =>
    match Encodable.decode (α := M) n with
    | none => []
    | some x => [(x, x)]
  refine ⟨schedule, ?_⟩
  intro x
  refine ⟨Encodable.encode x, ?_⟩
  simp [schedule, Encodable.encodek]

end AllThoseRamseyClasses.Lifts
