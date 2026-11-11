import AllThoseRamseyClasses.Published.TrackEPositivePatternGraphWeakBridge
import AllThoseRamseyClasses.Published.TrackEAmbientRelativeWeakSemanticAssembly
import PartiteConstruction.Functional.WholeMaskExactWeakLocalProjection2019

/-!
# Track E2: two canonical relational encodings give native ambient-relative
# weak homomorphisms on the SAME literal S and SAME f

The corrected 2019 complete-output whole-mask encoding has exact
whole-fibre semantics but cannot by itself see partially surviving
native weak outputs. The independent 2019 equality-pattern output
graph encodes each individual incidence but does not force equality
of whole target function fibres at source-closed inputs.

This theorem assumes BOTH positive OLD relational maps on the
SAME ACTUAL native partite source A, target B, weak set S and map f:
* a positive homomorphism of the induced pattern-tag expansion;
* a positive homomorphism of the induced complete whole-value mask.

They yield the TWO semantic clauses of the native
IsAmbientRelativeWeakHomomorphism A S B f without altering any
vertices, map, function values, or source subset.

The first clause uses the independently audited #973 decoder-on-
induced-S proof. The second uses the checked original-2019 exact
whole-fibre partial homomorphism from complete-mask OLD maps, and
#974's same-carrier semantic assembly.

This does NOT construct a single hybrid sparse Ramsey control with
both map conditions, show that its U-roots/strong amalgamation are
compatible, or protect native ambient irreducibles (the HE clause).
No 2019 original-lifting theorem conclusion is asserted.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The complete pattern-incidence and complete-output-mask
OLD maps on ONE source/target and ONE exact weak set S jointly imply
the CORRECT native positive-plus-full-when-closed ambient-relative
homomorphism. Both source and target must be genuine partite Systems;
no arbitrary relational picture is decoded by fiat.

The protected full-embedding condition of `IsAmbientRelativeWeakHE`
is not inferred here. -/
theorem ambientRelativeWeakHom_of_twoCanonicalPatternMaps
    {X Y : Type w} [Finite X]
    (A : FunctionalPartite.System L Parts X)
    (B : FunctionalPartite.System L Parts Y)
    (S : Set X) (f : S → Y)
    (hPattern :
      ((RelStructure.patternTagExpansion A.toStructure.patternGraph).induce S).IsHomomorphism
        (RelStructure.patternTagExpansion B.toStructure.patternGraph) f)
    (hWhole :
      ((A.toStructure.toNonemptyPartial.wholeMaskPatternGraph A.part).induce S).IsHomomorphism
        (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part) f) :
    IsAmbientRelativeWeakHomomorphism A.toStructure S B.toStructure f := by
  classical
  let Tagged := RelStructure.patternTagExpansion A.toStructure.patternGraph
  have hDecodedWeak :
      ((Structure.patternDecode (RelStructure.patternTagReduct Tagged)).weakInduce S).IsWeakHomomorphism
        B.toStructure f :=
    patternDecode_exactWeak_weakHom_of_positive_taggedHom
      Tagged S B.toStructure f hPattern
  have hNativeWeak :
      (A.toStructure.weakInduce S).IsWeakHomomorphism B.toStructure f := by
    constructor
    · intro R xs hx
      exact hDecodedWeak.1 R xs hx
    · intro F xs y hy
      have hNative :
          y.1 ∈ A.toStructure.func F (Subtype.val ∘ xs) := hy
      have hDecode :
          y.1 ∈ (Structure.patternDecode A.toStructure.patternGraph).func F
            (Subtype.val ∘ xs) :=
        (Structure.patternDecode_patternGraph_func
          A.toStructure F (Subtype.val ∘ xs) y.1).mpr hNative
      have hWeakDecode :
          y ∈ ((Structure.patternDecode
            (RelStructure.patternTagReduct Tagged)).weakInduce S).func F xs := by
        exact hDecode
      exact hDecodedWeak.2 F xs y hWeakDecode
  have hTransA :
      FibreTransversal A.toStructure.toNonemptyPartial A.part :=
    (nativeFunctionFibreTransversal_iff_partial
      A.toStructure A.part).mp A.funcTransversal
  have hWholePartial :
      PartialSetStructure.IsOriginalPartialHomomorphism
        (PartialSetStructure.wholeWeakInduce
          A.toStructure.toNonemptyPartial S)
        B.toStructure.toNonemptyPartial f :=
    PartialSetStructure.wholeWeakInduce_originalPartial_of_inducedOldHom
      A.toStructure.toNonemptyPartial A.part hTransA
      S B.toStructure.toNonemptyPartial B.part f hWhole
  exact ambientRelativeWeakHom_of_nativeWeak_and_wholePartial
    A.toStructure B.toStructure S f hNativeWeak hWholePartial

end AllThoseRamseyClasses.Published
