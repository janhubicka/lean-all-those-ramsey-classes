import AllThoseRamseyClasses.Lifts.NativeNonemptyPartialBridge
import PartiteConstruction.Structure.PartialSetFunctionsWholeWeak
import PartiteConstruction.Structure.WeakSubstructure

/-!
# Track E: exact native weak fibre survives genuine-partial weak decoding

The original native set-valued function structure interprets an
undefined input by an empty fibre. Its faithful genuine partial
Option(Set) representation uses none for that case and some U
for each NONEMPTY original fibre U.

The genuinely partial function library has a weak restriction
which CLIPS individual surviving values. It is essential that
this semantics agree on the EXACT original vertex subset S
with the native Structure.weakInduce S. In particular:

* an originally undefined input remains undefined;
* a nonempty input with no outputs in S becomes undefined;
* a nonempty input with at least one surviving output retains
  exactly the remaining output values;
* the richer defined-empty state never arises from a native
  input with nonempty value, so collapsing its domain bit
  leaves precisely the native weak function fibre.

This proves one exact semantic part of the corrected two-pass
2019 profile reduction: every weak test is measured on the
literal source S with exactly the same surviving native
set-valued function incidences. We do NOT switch to a
generated function-closure hull, a whole-fibre weak restriction,
or an ordinary EHN completion of the clipped weak test.

The independent rich partial whole-fibre restriction
PartialSetStructure.wholeWeakInduce has a DIFFERENT meaning:
it drops a whole function value if even one output escapes S.
It must not be substituted for clipping in this lemma.

This proof depends on PR #846's faithful Option(Set) encoding.
No class-level Ramsey theorem or sparse-control existence is
assumed or asserted.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- On each L-relation tuple, the literal weak restriction of
the faithful original-partial representation has exactly the
old native relation predicate on the same weak carrier S. -/
theorem nativeToNonemptyPartial_weakRel_iff
    {V : Type v} (A : Structure L V) (S : Set V)
    (R : L.RelSymbol) (xs : Fin (L.relArity R) → S) :
    (PartialSetStructure.collapseDomain
        ((nativeToNonemptyPartial A).weakInduce S)).rel R xs ↔
      (A.weakInduce S).rel R xs :=
  Iff.rfl

/-- The entire set-valued function OUTPUT FIBRE over an
EXACT weak input tuple in S agrees literally after the
faithful native-to-partial encoding, the genuine-partial
clipping weak restriction and the domain-bit collapse.

No defined-empty output state is spuriously introduced.
Both positive and negative output incidence reflection
are therefore available, not merely forward preservation. -/
theorem nativeToNonemptyPartial_weakFibre_eq
    {V : Type v} (A : Structure L V) (S : Set V)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S) :
    (PartialSetStructure.collapseDomain
        ((nativeToNonemptyPartial A).weakInduce S)).func F xs =
      (A.weakInduce S).func F xs := by
  classical
  let U : Set V := A.func F (Subtype.val ∘ xs)
  change
    (PartialSetStructure.weakValue S
      (if h : U.Nonempty then some U else none)).getD ∅ =
      {y : S | y.1 ∈ U}
  by_cases hU : U.Nonempty
  · by_cases hMeet : (U ∩ S).Nonempty
    · simp [PartialSetStructure.weakValue, hU, hMeet]
    · have hMissing : ({y : S | y.1 ∈ U} : Set S) = ∅ := by
        ext y
        constructor
        · intro hy
          exact (hMeet ⟨y.1, ⟨hy, y.2⟩⟩).elim
        · intro hy
          simp at hy
      simp [PartialSetStructure.weakValue, hU, hMeet, hMissing]
  · have hEmpty : U = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hU
    simp [PartialSetStructure.weakValue, hU, hEmpty]

end AllThoseRamseyClasses.Lifts
