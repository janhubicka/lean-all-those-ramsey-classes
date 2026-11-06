import AllThoseRamseyClasses.Published.FunctionalWithParts2019NativeKFaithfulImage
import PartiteConstruction.Functional.Operations
import PartiteConstruction.Functional.NativePartialClosure
import PartiteConstruction.Structure.PartialSetFunctionsClosed

/-!
# Track B: closed native functional restrictions commute with faithful Option(Set)

The canonical 2019 H image of a native functional class K in
FunctionalWithParts2019NativeKFaithfulImage has real native
set-valued function fibres, with empty fibres interpreted as
undefined in the genuine Option(Set) representation.

A weak restriction can delete function outputs and change the domain.
On a GENUINELY function-closed subset S, however, every ambient
function value over S stays in S. Consequently the native full
induced substructure followed by faithful nonempty-defined Option(Set)
conversion is literally the genuine partial-function closed
induced substructure followed by no change of carrier.

This identity permits a PRECISE native closed-heredity assumption on K
to transfer to closed heredity of its faithful genuinely partial
class H_K, with the same vertex parts. We do not infer any hereditary
axiom from a bare native K membership predicate.

Nonclosed weak tests remain ambient semi-closed tests, NOT canonical
K_H members, and the ambient-relative local-completion condition is
not supplied by this transfer.
-/

namespace StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The faithful nonempty-defined Option(Set) interpretation COMMUTES
LITERALLY with restriction to a genuinely NATIVE FUNCTION-CLOSED subset,
on the exact subtype S and including the entire function-domain bit.

In particular, no originally nonempty source value is dropped by
taking the closed native substructure. For an arbitrary nonclosed
S this equality would be false: one of the Option(Set) restrictions
might delete a function application whose output escaped S. -/
theorem toNonemptyPartial_induceClosed_eq
    (A : Structure L V) (S : Set V) (hS : A.IsClosed S) :
    (A.induce S hS).toNonemptyPartial =
      A.toNonemptyPartial.induceClosed S
        ((A.toNonemptyPartial_isClosed_iff S).mpr hS) := by
  classical
  have hFunc (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → S) :
      ((A.induce S hS).toNonemptyPartial).func F xs =
        (A.toNonemptyPartial.induceClosed S
          ((A.toNonemptyPartial_isClosed_iff S).mpr hS)).func F xs := by
    let U : Set V := A.func F (Subtype.val ∘ xs)
    have hSubset : U ⊆ S :=
      hS F (Subtype.val ∘ xs) (fun i => (xs i).property)
    have hNonemptyEq :
        ({y : S | y.1 ∈ U} : Set S).Nonempty ↔ U.Nonempty := by
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨y.1, hy⟩
      · rintro ⟨y, hy⟩
        exact ⟨⟨y, hSubset hy⟩, hy⟩
    change
      (if ({y : S | y.1 ∈ U} : Set S).Nonempty then
        some {y : S | y.1 ∈ U} else none) =
      (if U.Nonempty then some U else none).map
        (fun T => {y : S | y.1 ∈ T})
    by_cases hU : U.Nonempty
    · have hSub : ({y : S | y.1 ∈ U} : Set S).Nonempty :=
        hNonemptyEq.mpr hU
      simp [hU, hSub]
    · have hSub : ¬ ({y : S | y.1 ∈ U} : Set S).Nonempty := by
        intro h
        exact hU (hNonemptyEq.mp h)
      simp [hU, hSub]
  cases A with
  | mk rel func =>
    change PartialSetStructure.mk _ _ = PartialSetStructure.mk _ _
    congr 1
    funext F xs
    exact hFunc F xs

end StructuralRamsey.Structure

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {K : Structure.StructureClass (L := L)}

/-- Precisely the native heredity condition needed by the faithful
2019 H_K image: full native partite systems in K remain in K under
restriction to ANY genuine function-closed vertex subset.

This is not implied by arbitrary Stage membership; it is an explicit
class property to verify in concrete applications. It does not
require weak test carriers to be closed. -/
def NativeKClosedHereditary2019
    (K : Structure.StructureClass (L := L)) : Prop :=
  ∀ {X : Type v} [Finite X]
    (B : FunctionalPartite.System L Parts X),
    K B.toStructure →
    ∀ (S : Set X) (hS : B.toStructure.IsClosed S),
      K (B.induce S hS).toStructure

/-- Native closed-heredity transfers to GENUINE original-2019
closed-heredity of the exact faithful Option(Set) image H_K,
INCLUDING the original parts of all vertices.

The proof keeps the SAME native closed restriction `B.induce S hS`
and uses the literal commutation theorem above; it does not
assume that every arbitrary Option(Set) partial function arose
from the native `Structure` representation. -/
theorem nativeKFaithfulH_closedHereditary
    (K : Structure.StructureClass (L := L))
    (hK : NativeKClosedHereditary2019 (Parts := Parts) K) :
    GenuinePartiteClosedHereditary2019
      (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K) := by
  intro X hX A part hA S hS
  obtain ⟨B, hKB, hEq, hPart⟩ := hA
  subst A
  subst part
  have hNative : B.toStructure.IsClosed S :=
    (B.toStructure.toNonemptyPartial_isClosed_iff S).mp hS
  let BS : FunctionalPartite.System L Parts S := B.induce S hNative
  have hKBS : K BS.toStructure := hK B hKB S hNative
  refine ⟨BS, hKBS, ?_, rfl⟩
  exact (B.toStructure.toNonemptyPartial_induceClosed_eq S hNative).symm


/-- EXACT equivalence of native closed heredity and genuine 2019
closed heredity of the faithful class image H_K.

The backward direction uses that faithfully represented native
systems are determined by their Option(Set) representations:
`toNonemptyPartial.collapseDomain` is literally the identity on
native structures, so a genuine H_K witness for a CLOSED induced
source yields K membership for the EXACT corresponding native
closed restriction. No isomorphism-closure assumption is needed,
since the two native structures are equal on the same subtype S. -/
theorem nativeKFaithfulH_closedHereditary_iff
    (K : Structure.StructureClass (L := L)) :
    NativeKClosedHereditary2019 (Parts := Parts) K ↔
      GenuinePartiteClosedHereditary2019
        (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K) := by
  constructor
  · exact nativeKFaithfulH_closedHereditary K
  · intro hHer X hX B hKB S hS
    have hPartialClosed :
        B.toStructure.toNonemptyPartial.IsClosed S :=
      (B.toStructure.toNonemptyPartial_isClosed_iff S).mpr hS
    have hH :
        nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K
          ((B.toStructure.toNonemptyPartial).induceClosed S hPartialClosed)
          (B.part ∘ Subtype.val) :=
      hHer B.toStructure.toNonemptyPartial B.part
        ⟨B, hKB, rfl, rfl⟩ S hPartialClosed
    obtain ⟨C, hKC, hEqPartial, _⟩ := hH
    have hPartialEq :
        (B.induce S hS).toStructure.toNonemptyPartial =
          C.toStructure.toNonemptyPartial := by
      calc
        (B.induce S hS).toStructure.toNonemptyPartial =
            (B.toStructure.toNonemptyPartial).induceClosed
              S hPartialClosed :=
          B.toStructure.toNonemptyPartial_induceClosed_eq S hS
        _ = C.toStructure.toNonemptyPartial := hEqPartial
    have hNativeEq :
        (B.induce S hS).toStructure = C.toStructure := by
      have hCollapse :=
        congrArg PartialSetStructure.collapseDomain hPartialEq
      simpa only [Structure.toNonemptyPartial_collapseDomain]
        using hCollapse
    rw [hNativeEq]
    exact hKC



/-- Native free amalgamation classes are automatically native-closed
hereditary: this is the HEREDITARY field of the actual functional
FreeAmalgamationClass, applied to the genuine full native inclusion
of a function-closed induced partite system. No additional native
K heredity axiom is required for the verified EHN application. -/
theorem nativeKClosedHereditary_of_freeAmalgamationClass
    (K : Structure.StructureClass (L := L))
    (hFree : Structure.FreeAmalgamationClass K) :
    NativeKClosedHereditary2019 (Parts := Parts) K := by
  intro X hX B hB S hS
  exact hFree.hereditary hB
    (Structure.inclusion B.toStructure S hS)

/-- The verified native functional FreeAmalgamationClass axioms,
including its actual hereditary field, entail genuine
original-2019 closed heredity for the EXACT faithful Option(Set)
class H_K. The equality of closed native and genuine partial
restrictions is used by the preceding two-way transfer. -/
theorem nativeKFaithfulH_closedHereditary_of_freeAmalgamationClass
    (K : Structure.StructureClass (L := L))
    (hFree : Structure.FreeAmalgamationClass K) :
    GenuinePartiteClosedHereditary2019
      (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K) :=
  nativeKFaithfulH_closedHereditary (Parts := Parts) K
    (nativeKClosedHereditary_of_freeAmalgamationClass (Parts := Parts) K hFree)

/-- Exact 2019 tagged K_H membership among weak tests of an ACTUAL
native EHN Stage, under the same free-amalgamation-class hypothesis
ALREADY used by the verified native EHN attachment construction.

The tagged ambient test on S belongs to K_H iff S is genuinely
native function-closed. The proof does not need an external H
membership or extra class-heredity assumption. -/
theorem genuineEHNStage_freeAmalgamation_inducedK_iff_closed
    {D : Structure L Parts}
    (T : FunctionalPartite.EHN.Stage K D)
    (hFree : Structure.FreeAmalgamationClass K)
    (hPos : L.PositiveFuncArity)
    (S : Set T.Carrier) :
    canonicalGenuineTagged2019Class
        (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K)
        ((genuineEHNStageCanonical2019Tag T).induce S) ↔
      T.system.toStructure.IsClosed S :=
  genuineEHNStage_nativeKImage_inducedK_mem_iff_closed
    T (nativeKFaithfulH_closedHereditary_of_freeAmalgamationClass
      (Parts := Parts) K hFree) hPos S


/-- A genuinely native-closed-hereditary class K therefore has
the 2019 closed-test H/K image correspondence for EVERY actual EHN
Stage T in K, without taking an unrelated H-membership axiom and
without postulating hereditary closure of H_K separately.

Function arities are positive as required by the published 2019
fresh nonempty closure-root description. -/
theorem genuineEHNStage_nativeKHereditary_inducedK_iff_closed
    {D : Structure L Parts}
    (T : FunctionalPartite.EHN.Stage K D)
    (hK : NativeKClosedHereditary2019 (Parts := Parts) K)
    (hPos : L.PositiveFuncArity)
    (S : Set T.Carrier) :
    canonicalGenuineTagged2019Class
        (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K)
        ((genuineEHNStageCanonical2019Tag T).induce S) ↔
      T.system.toStructure.IsClosed S :=
  genuineEHNStage_nativeKImage_inducedK_mem_iff_closed
    T (nativeKFaithfulH_closedHereditary K hK) hPos S

end AllThoseRamseyClasses.Published
