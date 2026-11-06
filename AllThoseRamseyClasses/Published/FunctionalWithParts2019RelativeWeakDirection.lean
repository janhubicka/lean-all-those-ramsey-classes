import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeKCompletion
import PartiteConstruction.Functional.WholeMaskValueCoherenceHereditary2019
import PartiteConstruction.Functional.WholeMaskCoveredExactWeakLocalMap2019
import PartiteConstruction.Functional.WholeMaskCoveredFunctionalTarget2019

/-!
# Track C: the CORRECT logical direction for local class axiom transfer

The local-finiteness predicate has an implication as its outermost form:
if EVERY exact small weak test admits a completion, then the global
candidate has a copywise completion. To apply an intrinsic functional
version of this axiom to a 2019 ambient candidate, one needs a map
FROM ambient OLD local certificates TO intrinsic weak certificates,
not the (generally false) converse.

Here we prove that map for ORIGINAL-2019 source-defined genuinely
partial homomorphisms, provided the ambient OLD graph has UNIQUE
COMPLETE output values. The target is a genuine member of H, and the
tested carrier S and vertex map f are literally unchanged.

The proof does NOT claim that an arbitrary U-closed relational
candidate C has value coherence, a unique vertex part label, or
full-embedding protection of each intrinsically irreducible weak
functional test. Those are distinct remaining obligations for a
class-level theorem. No witness is marked full-functional unless
undefined source operation states are correctly reflected.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- A weaker genuine H-valued certificate for the ORIGINAL decoded
partial functions on the exact weak carrier S, using the published
source-defined rather than domain-reflecting map convention. -/
def HasGenuineIntrinsicWeakPositiveCompletion
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (S : Set V) : Prop :=
  ∃ (X : Type w) (_ : Finite X)
    (Target : PartialSetStructure L X) (partTarget : X → Parts),
      H Target partTarget ∧ FibreTransversal Target partTarget ∧
      ∃ (f : S → X),
        IsOriginalPartialHomomorphism
          (wholeWeakInduce (wholeMaskOriginalDecode C) S) Target f

/-- Every ambient tagged 2019 local H-certificate yields an intrinsic
SOURCE-DEFINED genuinely partial functional local H-certificate on
EXACTLY S, provided the ambient source's complete output values are
unique. The SAME map f and genuine H target are reused.

This direction alone is insufficient for a general local-class theorem:
one still needs source normalization/coherence from the whole
candidate's corrected closed-irreducible coverage, and preservation of
the full protected-copy map predicate rather than only positive data.
-/
theorem relative_implies_intrinsicWeakPositive_of_unique
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (S : Set V)
    (hUnique : HasUniqueWholeMaskValues (wholeMaskTagReduct C))
    (hRelative :
      HasGenuinePartiteTagged2019RelativeCompletion H (C.induce S)) :
    HasGenuineIntrinsicWeakPositiveCompletion H C S := by
  rcases hRelative with
    ⟨X, hFinite, Target, targetPart, hH, hTr, _, f, hTagged⟩
  letI : Finite X := hFinite
  have hOld :
      ((wholeMaskTagReduct C).induce S).IsHomomorphism
        (withPartsWholeMaskOld Target targetPart) f := by
    intro R xs hR
    exact hTagged.1 (.inl R) xs hR
  have hPlus :
      IsOriginalPartialHomomorphism
        (wholeWeakInduce
          ((wholeMaskTagReduct C).wholeMaskPartialDecode) S)
        (Target.withParts targetPart) f :=
    wholeMaskPartialDecode_weak_originalPartial_of_inducedOldHom
      (wholeMaskTagReduct C) hUnique S
      (Target.withParts targetPart) targetPart f hOld
  have hOriginal :
      IsOriginalPartialHomomorphism
        (wholeWeakInduce (wholeMaskOriginalDecode C) S)
        Target f := by
    constructor
    · intro R xs hR
      exact hPlus.1 (.inl (ULift.up R)) xs hR
    · intro F xs U hU
      exact hPlus.2 (ULift.up F) xs U hU
  exact ⟨X, hFinite, Target, targetPart,
    hH, hTr, f, hOriginal⟩

end AllThoseRamseyClasses.Published
