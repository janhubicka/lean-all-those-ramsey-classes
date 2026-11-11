import AllThoseRamseyClasses.Published.TrackEAmbientRelativeWeakSemanticAssembly
import PartiteConstruction.Functional.OutputPartSingletonization

/-!
# Track E2: whole-fibre OLD local maps suffice after output-part singletonization

The clipped native weak substructure and the complete/whole-fibre
2019 weak restriction differ on MULTIVALUED fibres that cross S.
But if every primitive output fibre is EMPTY OR A SINGLETON, then
any output surviving S forces the ENTIRE original fibre inside S.

Thus an original-2019 source-defined partial homomorphism of the
WHOLE-fibre weak faithful encoding on the SAME S immediately yields
native positive weak preservation (on every surviving value), as
well as the complete target-fibre equality on wholly retained
original inputs. Hence the NATIVE IsAmbientRelativeWeakHomomorphism
condition follows without an extra positive-incidence graph language.

The canonical `FunctionalPartite.System.splitOutputParts` construction
already turns any transversal multivalued native System into a
singleton-output language indexed by its output part, on exactly the
SAME vertex carrier and same part map. A second theorem specializes
the bridge to these split partite Systems, with no restriction to
singleton-valued ORIGINAL functions.

This is a potentially simpler E2 route than dual relational encoding:
reuse the verified 2019 whole-mask machinery in the OUTPUT-PART-SPLIT
functional language.  It is not yet a proof that the two-pass sparse
construction gives compatible split-age completions, nor the protected
ambient irreducible clause of IsAmbientRelativeWeakHE; these remain
independent.

No original proof text is edited, no weak test closure hull is taken.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.FunctionalPartite

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- On genuinely singleton-valued native sources, a source-defined
complete WHOLE-fibre partial map already preserves every surviving
native weak output, because any surviving source output exhausts
its entire original singleton fibre. Combined with the existing
whole-fibre equality lemma, this is the ambient-relative WEAK
homomorphism, on the literal same source set and vertex map. -/
theorem ambientRelativeWeakHom_of_singletonWholePartial
    (A : Structure L V) (B : Structure L W)
    (hSingle : A.SingletonValued)
    (S : Set V) (f : S → W)
    (hWhole : PartialSetStructure.IsOriginalPartialHomomorphism
      (PartialSetStructure.wholeWeakInduce A.toNonemptyPartial S)
      B.toNonemptyPartial f) :
    IsAmbientRelativeWeakHomomorphism A S B f := by
  classical
  have hNativeWeak :
      (A.weakInduce S).IsWeakHomomorphism B f := by
    constructor
    · intro R xs hx
      exact hWhole.1 R xs hx
    · intro F xs y hy
      let U : Set V := A.func F (Subtype.val ∘ xs)
      let US : Set S := {z : S | z.1 ∈ U}
      have hMem : y.1 ∈ U := hy
      have hSub : U ⊆ S := by
        intro z hz
        have hzEq : z = y.1 :=
          hSingle F (Subtype.val ∘ xs) z y.1 hz hMem
        rw [hzEq]
        exact y.2
      have hNonempty : U.Nonempty := ⟨y.1, hMem⟩
      have hSome :
          A.toNonemptyPartial.func F (Subtype.val ∘ xs) = some U := by
        change (if U.Nonempty then some U else none) = some U
        exact if_pos hNonempty
      have hWholeVal :
          (PartialSetStructure.wholeWeakInduce A.toNonemptyPartial S).func
            F xs = some US := by
        change PartialSetStructure.wholeWeakValue S
          (A.toNonemptyPartial.func F (Subtype.val ∘ xs)) = some US
        rw [hSome]
        exact PartialSetStructure.wholeWeakValue_of_subset S U hSub
      have hTarget :
          B.toNonemptyPartial.func F (f ∘ xs) =
            some (Structure.imageSet f US) :=
        hWhole.2 F xs US hWholeVal
      have hImage : f y ∈ Structure.imageSet f US := ⟨y, hMem, rfl⟩
      have hBNonempty : (B.func F (f ∘ xs)).Nonempty := by
        by_contra hn
        have hNone : B.toNonemptyPartial.func F (f ∘ xs) = none := by
          change (if (B.func F (f ∘ xs)).Nonempty then
            some (B.func F (f ∘ xs)) else none) = none
          simp [hn]
        rw [hNone] at hTarget
        cases hTarget
      have hEq :
          B.func F (f ∘ xs) = Structure.imageSet f US := by
        change (if (B.func F (f ∘ xs)).Nonempty then
          some (B.func F (f ∘ xs)) else none) =
          some (Structure.imageSet f US) at hTarget
        simpa only [if_pos hBNonempty, Option.some.injEq] using hTarget
      rw [hEq]
      exact hImage
  exact ambientRelativeWeakHom_of_nativeWeak_and_wholePartial
    A B S f hNativeWeak hWhole

/-- Every genuine multivalued partite System becomes singleton-valued
in each output-part-indexed primitive function. Thus ONE original
2019 whole-fibre weak partial local map of the SPLIT systems suffices
for correct native ambient-relative weak semantics, with no additional
positive relation symbols. Source/output parts and weak carrier stay
exactly unchanged. -/
theorem splitOutputParts_ambientRelativeWeakHom_of_wholePartial
    {Parts : Type*}
    (A : FunctionalPartite.System L Parts V)
    (B : FunctionalPartite.System L Parts W)
    (S : Set V) (f : S → W)
    (hWhole : PartialSetStructure.IsOriginalPartialHomomorphism
      (PartialSetStructure.wholeWeakInduce
        (A.splitOutputParts).toStructure.toNonemptyPartial S)
      (B.splitOutputParts).toStructure.toNonemptyPartial f) :
    IsAmbientRelativeWeakHomomorphism
      (A.splitOutputParts).toStructure S
      (B.splitOutputParts).toStructure f := by
  exact ambientRelativeWeakHom_of_singletonWholePartial
    (A.splitOutputParts).toStructure
    (B.splitOutputParts).toStructure
    A.splitOutputParts_singletonValued S f hWhole

end AllThoseRamseyClasses.Published
