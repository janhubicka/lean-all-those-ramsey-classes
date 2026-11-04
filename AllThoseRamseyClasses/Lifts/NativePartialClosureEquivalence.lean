import AllThoseRamseyClasses.Lifts.NativeNonemptyPartialBridge
import PartiteConstruction.Structure.PartialSetFunctionsClosed

/-!
# Track E: native and genuine-partial closure coincide exactly

For the faithful nonempty-fibre native-to-Option(Set) encoding,
an original native function input is undefined exactly when
its complete set-valued output fibre is empty. A defined input
carries the full nonempty original fibre, never an invented
defined-empty value.

Therefore a literal vertex subset S of the old native carrier
is closed under EVERY old set-valued function precisely when S
is closed in the genuine partial Option(Set) representation.
This uses full output fibres, not a graph-closure approximation;
no finite generation or arity hypothesis is imposed.

Closure equivalence is an essential independent dictionary
for transferring the verified 2019 U-closed relational profile
machinery to the alternative finite-family native lifted age.
It does NOT assert that an arbitrary tagged relational
completion decodes to a valid native maximal trace, nor that
weakly induced tests are function-closed.

This is about genuine FULL closed substructures, not the
separately verified clipped weak-partial restriction.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- EXACT closure preservation and reflection for every literal
native vertex set S under the faithful partial encoding.

The native notion includes all output values of every old
function whose entire input tuple lies in S. The partial
notion imposes the same requirement only on genuinely
defined inputs, which here are exactly the nonempty old
fibres; empty/undefined inputs impose no extra closure. -/
theorem nativeToNonemptyPartial_isClosed_iff
    {V : Type v} (A : Structure L V) (S : Set V) :
    (nativeToNonemptyPartial A).IsClosed S ↔
      A.IsClosed S := by
  classical
  constructor
  · intro hPartial F xs hArgs y hy
    have hNon : (A.func F xs).Nonempty := ⟨y, hy⟩
    have hSome :
        (nativeToNonemptyPartial A).func F xs =
          some (A.func F xs) := by
      simp [nativeToNonemptyPartial, hNon]
    exact hPartial F xs (A.func F xs) hArgs hSome hy
  · intro hNative F xs T hArgs hDefined
    by_cases hNon : (A.func F xs).Nonempty
    · have hEq : A.func F xs = T := by
        have hs :
            some (A.func F xs) = some T := by
          simpa [nativeToNonemptyPartial, hNon] using hDefined
        exact Option.some.inj hs
      subst T
      exact hNative F xs hArgs
    · have hNone :
          (nativeToNonemptyPartial A).func F xs = none := by
        simp [nativeToNonemptyPartial, hNon]
      rw [hNone] at hDefined
      cases hDefined

/-- No canonical faithful native encoding can contain the
genuine-partial defined-empty state. This state is distinct
from undefined in the richer category; ruling it out on the
image is what permits the native collapse decoder. -/
theorem nativeToNonemptyPartial_no_definedEmpty
    {V : Type v} (A : Structure L V)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V) :
    (nativeToNonemptyPartial A).func F xs ≠
      some (∅ : Set V) := by
  classical
  by_cases hNon : (A.func F xs).Nonempty
  · intro h
    have hEq : A.func F xs = ∅ := by
      have hs : some (A.func F xs) = some (∅ : Set V) := by
        simpa [nativeToNonemptyPartial, hNon] using h
      exact Option.some.inj hs
    obtain ⟨y, hy⟩ := hNon
    rw [hEq] at hy
    simp at hy
  · simp [nativeToNonemptyPartial, hNon]

end AllThoseRamseyClasses.Lifts
