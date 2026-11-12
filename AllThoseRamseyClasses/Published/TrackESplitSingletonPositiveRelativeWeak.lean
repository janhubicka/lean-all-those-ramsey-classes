import AllThoseRamseyClasses.Published.TrackEDualEncodedAmbientRelativeWeakMap
import PartiteConstruction.Functional.OutputPartSingletonization
import PartiteConstruction.Functional.AmbientRelativeWeakFunctions

/-!
# Track E2: positive weak graph maps already give relative fibre equality with singleton targets

The native relative weak homomorphism requires two laws on the exact
weak S: (1) positive preservation of all surviving output incidences,
and (2) image equality of full nonempty source fibres wholly in S.

When the TARGET is singleton-valued in each primitive function, (2)
is automatic from (1): a fully retained nonempty source fibre has
some positive output and hence its weak image contains a target
output. All target outputs must equal it by singleton-valuedness,
so the entire target fibre is exactly the source image. No source
singleton hypothesis, source injectivity, output-part mask, or
undefined-domain reflection is needed for this split-language fact.

For a genuine native partite System B, canonical output-part
singletonization always makes B's target fibres singleton-valued.
The verified tagged equality-pattern positive decoder supplies (1)
from ONE positive relational map of the literal ambient tagged
induced weak S into the canonical split target. Thus it supplies the
full split-language IsAmbientRelativeWeakHomomorphism, without an
independent whole-value map in the split language.

This is a semantic simplification, not full weak HE: the irreducible
FULL-copy protection clause and a sparse witness providing an actual
positive tagged local map remain separate. The old ORIGINAL
multivalued output-part mask must still be carried to exclude phantom
parts when descending back to the original language (#1003).
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {V W : Type v}

/-- For an arbitrary set-valued SOURCE and singleton-valued TARGET,
positive native weak homomorphism already forces exact complete
target fibre equality for every nonempty source input whose entire
ambient output set belongs to S. Works for all primitive arities
including nullaries; neither f nor the source fibres must be injective
or singleton-valued. -/
theorem ambientRelativeWeakHom_of_nativeWeak_targetSingleton
    (A : Structure L V) (B : Structure L W)
    (hSingleTarget : B.SingletonValued)
    (S : Set V) (f : S → W)
    (hWeak : (A.weakInduce S).IsWeakHomomorphism B f) :
    IsAmbientRelativeWeakHomomorphism A S B f := by
  refine ⟨hWeak, ?_⟩
  intro F xs hNonempty hAll
  obtain ⟨a, ha⟩ := hNonempty
  let aS : S := ⟨a, hAll a ha⟩
  have haWeak : aS ∈ (A.weakInduce S).func F xs := ha
  have haTarget : f aS ∈ B.func F (f ∘ xs) :=
    hWeak.2 F xs aS haWeak
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hWeak.2 F xs z hz
  · intro hy
    have hEq : y = f aS :=
      hSingleTarget F (f ∘ xs) y (f aS) hy haTarget
    exact ⟨aS, haWeak, hEq.symm⟩

/-- A SINGLE positive relational map on the canonical split-function
equality-pattern tagged source, restricted to the literal S, already
gives the complete native ambient-relative weak HOMOMORPHISM in the
split language. The source need not be function-closed; all partially
surviving outputs are kept positively. No separate split OLD
complete-value/partial-homomorphism map is needed.

The stronger IsAmbientRelativeWeakHE still requires protection of
FULL ambient irreducible split tests. -/
theorem splitAmbientRelativeWeakHom_of_positivePatternTaggedHom
    {Parts : Type w}
    {X Y : Type v} [Finite X]
    (A : FunctionalPartite.System L Parts X)
    (B : FunctionalPartite.System L Parts Y)
    (S : Set X) (f : S → Y)
    (hTagged :
      ((patternTagExpansion
        A.splitOutputParts.toStructure.patternGraph).induce S).IsHomomorphism
        (patternTagExpansion
          B.splitOutputParts.toStructure.patternGraph) f) :
    IsAmbientRelativeWeakHomomorphism
      A.splitOutputParts.toStructure S
      B.splitOutputParts.toStructure f := by
  classical
  let AA := A.splitOutputParts
  let BB := B.splitOutputParts
  let Tagged := patternTagExpansion AA.toStructure.patternGraph
  have hDecodedWeak :
      ((Structure.patternDecode (patternTagReduct Tagged)).weakInduce S).IsWeakHomomorphism
        BB.toStructure f :=
    patternDecode_exactWeak_weakHom_of_positive_taggedHom
      Tagged S BB.toStructure f hTagged
  have hWeak :
      (AA.toStructure.weakInduce S).IsWeakHomomorphism BB.toStructure f := by
    constructor
    · intro R xs hx
      exact hDecodedWeak.1 R xs hx
    · intro F xs y hy
      have hNative :
          y.1 ∈ AA.toStructure.func F (Subtype.val ∘ xs) := hy
      have hDecode :
          y.1 ∈ (Structure.patternDecode AA.toStructure.patternGraph).func F
            (Subtype.val ∘ xs) :=
        (Structure.patternDecode_patternGraph_func
          AA.toStructure F (Subtype.val ∘ xs) y.1).mpr hNative
      have hWeakDecode :
          y ∈ ((Structure.patternDecode
            (patternTagReduct Tagged)).weakInduce S).func F xs :=
        hDecode
      exact hDecodedWeak.2 F xs y hWeakDecode
  exact ambientRelativeWeakHom_of_nativeWeak_targetSingleton
    AA.toStructure BB.toStructure B.splitOutputParts_singletonValued
    S f hWeak

end AllThoseRamseyClasses.Published
