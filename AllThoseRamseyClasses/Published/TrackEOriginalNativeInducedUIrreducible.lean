import AllThoseRamseyClasses.Published.TrackEActualCoveredInducedUIrreducible
import PartiteConstruction.Functional.WholeMaskCoveredFunctionalTarget2019
import PartiteConstruction.Functional.PartialSetFunctionsPartPredicates2019
import PartiteConstruction.Structure.IrreducibleHomImage

/-!
# Track E: original native full irreducibles give actual tagged U-tests

The 2019 final whole-mask tagged structure is written in the language
(L.withParts P), while the desired native homomorphism-embedding in
Appendix A tests irreducible copies in the ORIGINAL function language L.

The preceding Track E exact-tagged irreducibility lemma acts on the
full part-labelled native decoder. Instead of postulating
irreducibility after adding unary relations, apply the generic
verified native closed-cover transfer DIRECTLY to the unlabelled
original decoder on the SAME exact vertex set S.

Relative U-closedness and complete relation/function localization
come from the genuine PART-LABELLED final tagged C; forgetting the
unary labels changes neither original relations nor primitive
function values. On every exact full native S, these properties
descend literally to the native original-language restriction.
No canonical tagged E lift or closure hull is inserted.

This is still only the geometric U-irreducibility of the ACTUAL
induced tagged test. Selected global-control map protection and the
original 2019 native HE endpoint are separate.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- An actual full native irreducible exact S in the ORIGINAL function
language, with the final decoded closedness, is intrinsically
U-irreducible in the genuine part-labelled final tagged 2019 target C.
The original S is never replaced by a generated hull or a canonical
re-encoding of C. -/
theorem wholeMaskCovered_originalNativeInducedUIrreducible
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (basePart : W → P)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) X),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (S : Set V)
    (hS : ((wholeMaskOriginalDecode C).collapseDomain).IsClosed S)
    (hNativeIrred :
      (((wholeMaskOriginalDecode C).collapseDomain).induce S hS).Irreducible) :
    IsUIrreducible ((L.withParts P).wholeMaskClosureRules P)
      (C.induce S) := by
  let Plus : PartialSetStructure (L.withParts P) V :=
    (wholeMaskTagReduct C).wholeMaskPartialDecode
  let Native : Structure L V :=
    (wholeMaskOriginalDecode C).collapseDomain
  have hOrigClosed :
      (wholeMaskOriginalDecode C).IsClosed S :=
    ((wholeMaskOriginalDecode C).isClosed_iff_collapseDomain_isClosed S).mpr hS
  have hPlusClosed : Plus.IsClosed S := by
    intro F xs T hxs hVal
    exact hOrigClosed F.down xs T hxs hVal
  have hPlusNativeClosed : Plus.collapseDomain.IsClosed S :=
    (Plus.isClosed_iff_collapseDomain_isClosed S).mp hPlusClosed
  have hTagClosed :
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) (C.induce S) :=
    wholeMaskCovered_decodedClosed_to_inducedUClosed
      C (Base.withParts basePart) basePart
      hC (hPos.withParts) hCover S hPlusClosed
  refine nativeIrreducible_implies_uIrreducible_of_sideTransfer
    ((L.withParts P).wholeMaskClosureRules P)
    (C.induce S) (Native.induce S hS)
    hTagClosed hNativeIrred ?_ ?_
  · intro X hX
    have hPlusX :
        (Plus.collapseDomain.induce S hPlusNativeClosed).IsClosed X :=
      wholeMaskCovered_inducedUSubstructure_to_nativeClosed
        C (Base.withParts basePart) basePart
        hC (hPos.withParts) hCover S hPlusClosed X hX
    intro F xs hxs y hy
    exact hPlusX (ULift.up F) xs hxs hy
  · intro X Y hTuple
    constructor
    · intro R xs hRel
      exact hTuple (.inl (.inl (.inl (ULift.up R)))) xs hRel
    · intro F xs y hy
      exact wholeMaskCovered_inducedNativeFunctionIncident_side
        C (Base.withParts basePart) basePart
        hC (hPos.withParts) hCover
        S hPlusClosed X Y hTuple (ULift.up F) xs y hy

/-- The exact range of EVERY genuinely irreducible full native E-copy
of the final ORIGINAL decoded structure is intrinsically U-irreducible
as an induced test of the ACTUAL noncanonical tagged final witness.

Full function-closure of the range and irreducibility of the genuine
native induced structure follow from the EXISTING full-embedding range
and surjective-image theorems. The tested carrier is literally range(e);
there is no image hull, canonical replacement, or alternate map. -/
theorem wholeMaskCovered_originalNativeIrredCopy_UIrreducible
    (C : RelStructure ((L.withParts P).wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (basePart : W → P)
    (hC : IsUClosed ((L.withParts P).wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure ((L.withParts P).wholeMaskTagLanguage P) X),
      IsUClosed ((L.withParts P).wholeMaskClosureRules P) Test →
      IsUIrreducible ((L.withParts P).wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    {T : Type v} (E : Structure L T)
    (hE : E.Irreducible)
    (e : Structure.Embedding E
      ((wholeMaskOriginalDecode C).collapseDomain)) :
    IsUIrreducible ((L.withParts P).wholeMaskClosureRules P)
      (C.induce (Set.range e)) := by
  exact wholeMaskCovered_originalNativeInducedUIrreducible
    C Base basePart hC hPos hCover
    (Set.range e) e.range_isClosed
    (hE.range_homomorphism e.isHomomorphism)


end AllThoseRamseyClasses.Published
