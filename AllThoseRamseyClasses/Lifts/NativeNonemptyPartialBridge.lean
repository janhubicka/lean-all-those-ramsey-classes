import PartiteConstruction.Structure.PartialSetFunctions
import PartiteConstruction.Functional.OriginalPartialSemantics

/-!
# Track E: faithful bridge from native nonempty fibres to genuine partial functions

The native Lean function structure interprets an operation as
  F : V^r → Set V
with empty output meaning undefined. The richer 2019 two-pass
profile construction uses the truly partial representation
  F : V^r → Option (Set V),
which can additionally distinguish a DEFINED empty value from
an undefined input.

A native structure embeds canonically into the full subcategory
of genuinely partial structures whose DEFINED values are
NONEMPTY: use none exactly for the empty native fibre and
some S exactly for nonempty S. This leaves every old relation
unchanged, and collapsing the additional domain bit recovers
the original native structure.

Crucially, a FULL native functional embedding becomes an actual
FULL genuine-partial embedding; equality of COMPLETE native
output fibres gives equality of the Option values, including
exact domain reflection. We never conflate some empty with none
inside the richer category; instead the former does not occur
on the image of the native embedding.

This is a faithful structural input bridge for investigating
the already-verified coordinated 2019 two-pass profiled
RELATIONAL sparsening route. It does not prove that the final
profile construction preserves this full subcategory, nor the
finite-family Ramsey theorem. That decoding/normality issue
remains an explicit proof obligation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}}

/-- Canonical original-partial representation of a native
set-valued function structure whose empty fibres mean
UNDEFINED operations. Nonempty fibres retain their whole
original output set. -/
noncomputable def nativeToNonemptyPartial
    {V : Type v} (A : Structure L V) :
    PartialSetStructure L V where
  rel := A.rel
  func F xs :=
    if h : (A.func F xs).Nonempty then
      some (A.func F xs)
    else none

/-- In the canonical partial representation, the domain
is EXACTLY the set of inputs carrying a nonempty native
set-valued function fibre. Thus no additional independent
domain information is invented. -/
theorem nativeToNonemptyPartial_defined_iff
    {V : Type v} (A : Structure L V)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V) :
    (nativeToNonemptyPartial A).Defined F xs ↔
      (A.func F xs).Nonempty := by
  classical
  unfold PartialSetStructure.Defined nativeToNonemptyPartial
  by_cases h : (A.func F xs).Nonempty
  · simp [h]
  · simp [h]

/-- A FULL native embedding transports the same exact complete
output fibres into the richer original-partial category.
In particular it reflects the input domain, including
undefined (empty) native fibres. This is stronger than a
weak EHN projection. -/
noncomputable def nativeToNonemptyPartialEmbedding
    {VA : Type v} {VB : Type w}
    {A : Structure L VA} {B : Structure L VB}
    (e : Structure.Embedding A B) :
    PartialSetStructure.Embedding
      (nativeToNonemptyPartial A)
      (nativeToNonemptyPartial B) where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R xs
    exact e.map_rel_iff R xs
  map_func := by
    intro F xs
    by_cases hA : (A.func F xs).Nonempty
    · have hB : (B.func F (e ∘ xs)).Nonempty := by
        obtain ⟨y, hy⟩ := hA
        refine ⟨e y, ?_⟩
        rw [← e.map_func F xs]
        exact ⟨y, hy, rfl⟩
      simpa [nativeToNonemptyPartial, hA, hB]
        using e.map_func F xs
    · have hAEmpty : A.func F xs = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hA
      have hBEmpty : B.func F (e ∘ xs) = ∅ := by
        rw [← e.map_func F xs, hAEmpty]
        simp [Structure.imageSet]
      simp [nativeToNonemptyPartial, hAEmpty, hBEmpty]

/-- All native relation tuples and function fibres are
recovered literally by collapsing the extra independent
domain bit of the canonical partial representation.
There are no defined-empty input values in its image. -/
theorem collapseDomain_nativeToNonemptyPartial
    {V : Type v} (A : Structure L V) :
    PartialSetStructure.collapseDomain
      (nativeToNonemptyPartial A) = A := by
  cases A with
  | mk rel func =>
    congr 1
    funext F xs
    change (if h : (func F xs).Nonempty then
      some (func F xs) else none).getD ∅ = func F xs
    by_cases h : (func F xs).Nonempty
    · simp [h]
    · have hEmpty : func F xs = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp h
      simp [h, hEmpty]

end AllThoseRamseyClasses.Lifts
