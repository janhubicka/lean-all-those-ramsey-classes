import AllThoseRamseyClasses.Lifts.NativeNonemptyPartialBridge
import PartiteConstruction.Functional.OriginalPartialSemantics

/-!
# Track E: native EHN projections are genuine original partial homomorphisms

The Lean native set-valued functional interface encodes an UNDEFINED
input by the empty fibre. The faithful nativeToNonemptyPartial
representation of that interface uses Option (Set V):
  native empty fibre       -> none;
  native nonempty fibre    -> some of the complete original value set.
It never introduces a defined-empty value.

An EHN projection p:A->B is globally weak but preserves the entire
output fibre of every source-defined input. In the richer genuine
partial-function language, this is EXACTLY the 2019
PartialSetStructure.IsOriginalPartialHomomorphism condition:
defined source inputs preserve all output values, including equality
onto the target output fibre, while undefined inputs impose no
domain-reflection condition.

This theorem is a faithful connection to the existing
two-pass whole-mask profiled relational sparsening route.
It does NOT assert that an EHN map is globally full or
injective, that target domain bits reflect on undefined inputs,
or that an arbitrary relational profile target decodes to a
native functional structure. Those later steps remain open.

This file depends on the preceding native-to-Option embedding
bridge (PR #846), which must pass its independent CI gate.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Every genuine native EHN homomorphism-embedding
induces a faithful ORIGINAL-2019 source-defined partial
homomorphism on its Option(Set)-valued representations.

Only nonempty *source* fibres must be mapped ONTO
complete target fibres. No reflection of undefined
inputs, injectivity or preservation of spurious
weakly clipped function data is required. -/
theorem nativeEHN_toNonemptyPartial_originalHom
    {VA VB : Type v}
    {A : Structure L VA} {B : Structure L VB}
    {p : VA → VB}
    (hp : A.IsEHNHomomorphismEmbedding B p) :
    PartialSetStructure.IsOriginalPartialHomomorphism
      (nativeToNonemptyPartial A)
      (nativeToNonemptyPartial B) p := by
  classical
  constructor
  · intro R xs hR
    exact hp.1.1 R xs hR
  · intro F xs S hSome
    have hSource : (A.func F xs).Nonempty := by
      by_contra hNo
      have hNone :
          (nativeToNonemptyPartial A).func F xs = none := by
        simp [nativeToNonemptyPartial, hNo]
      rw [hNone] at hSome
      cases hSome
    have hS : A.func F xs = S := by
      simpa [nativeToNonemptyPartial, hSource]
        using hSome
    have hFunc :
        Structure.imageSet p (A.func F xs) =
          B.func F (p ∘ xs) :=
      hp.toOriginalPartial.1.2 F xs hSource
    have hTarget : (B.func F (p ∘ xs)).Nonempty := by
      obtain ⟨y, hy⟩ := hSource
      refine ⟨p y, ?_⟩
      rw [← hFunc]
      exact ⟨y, hy, rfl⟩
    change (if h : (B.func F (p ∘ xs)).Nonempty then
      some (B.func F (p ∘ xs)) else none) =
      some (Structure.imageSet p S)
    rw [dif_pos hTarget]
    exact congrArg some
      (hFunc.symm.trans (congrArg (Structure.imageSet p) hS))

end AllThoseRamseyClasses.Lifts
