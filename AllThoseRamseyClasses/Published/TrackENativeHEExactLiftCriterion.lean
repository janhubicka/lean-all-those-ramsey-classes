import AllThoseRamseyClasses.Published.FunctionalWithParts2019GlobalProtectedControl
import AllThoseRamseyClasses.Published.TrackEActualStandardSystemSparseWitness
import AllThoseRamseyClasses.Published.FunctionalWithParts2019NativeKRamseyDescent
import PartiteConstruction.Functional.TrackESourceDefinedPartialIff

/-!
# Track E: the EXACT missing native global-HE test-lift condition

The corrected 2019 sparse Ramsey construction produces an actual tagged
induced-closed U-homomorphism-embedding hTag on a SELECTED control map f.
The genuine native decoder establishes only a source-defined global
homomorphism on the same f.

This module verifies the precise conditional final upgrade:

* for EVERY native irreducible FULL E-copy in the actual final native
  partite System D, use the literal E carrier and pulled-back part map;
* assume its complete canonical whole-mask tagged presentation embeds
  FULLY into the SAME actual tagged C by precisely the original E-copy
  vertex map, and is intrinsically U-irreducible;
* apply the tagged corrected U-HE on that very test, then the already
  verified canonical full-function embedding decoder to get a FULL
  original native E-copy in the canonical original control, on SAME f.

Thus only the exact canonical-tagged test lift is LEFT AS AN EXPLICIT
HYPOTHESIS. No extra choice of control map, generated hull, false
domain reflection, strict mixed-root B-tree, or unproved native-test
canonicality has been smuggled into the claim.

The independent regression in partite-construction PR #572 shows
why merely knowing that f is a source-defined homomorphism plus B
coverage does not establish this conclusion.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.Structure.TrackENativePartiteFinalArrow
open StructuralRamsey.Structure.TrackENativePartialFullFaithfulness

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Full genuine-partial embeddings pull back function-output
transversality to EXACT source vertices and the pulled-back actual
part map. This does not require the source to be finite, or any
positive-function-arity, nonempty-fibre or closure assumption. -/
theorem fibreTransversal_pullback_fullEmbedding
    {X Y : Type w}
    (A : PartialSetStructure L X) (B : PartialSetStructure L Y)
    (e : PartialSetStructure.Embedding A B)
    (partB : Y → Parts)
    (hTransB : FibreTransversal B partB) :
    FibreTransversal A (partB ∘ e.toFun) := by
  intro F xs U hValue y hy z hz hPart
  have hMapped :
      B.func F (e.toFun ∘ xs) =
        some (Structure.imageSet e.toFun U) := by
    simpa only [hValue, Option.map_some] using (e.map_func F xs).symm
  have hY : e.toFun y ∈ Structure.imageSet e.toFun U :=
    ⟨y, hy, rfl⟩
  have hZ : e.toFun z ∈ Structure.imageSet e.toFun U :=
    ⟨z, hz, rfl⟩
  have hEq : e.toFun y = e.toFun z :=
    hTransB F (e.toFun ∘ xs) (Structure.imageSet e.toFun U)
      hMapped (e.toFun y) hY (e.toFun z) hZ hPart
  exact e.injective hEq

/-- Exact SAME-MAP HE upgrade from the actual corrected tagged control.

The `hExactLift` assumption is the missing geometric statement.
It demands a FULL canonical-tagged embedding of each native full
irreducible E-copy into the actual tagged C, with the identical
vertex map, and requires U-irreducibility of that tagged test.
It is NOT inferred here from protected B coverage or from the
mere existence of the decoded native target.

The conclusion is the literal original 2019 native
`IsOriginalPartialHomomorphismEmbedding`: the selected f is a
source-defined whole-value homomorphism AND protects EVERY native
irreducible FULL E-copy. It does not become a total-fibre map.
-/
theorem nativeOriginalPartialHE_of_taggedHE_and_exactCanonicalLifts
    {V W : Type w} [Finite V] [Finite W]
    (D : FunctionalPartite.System L Parts V)
    (Target : FunctionalPartite.System L Parts W)
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (f : V → W)
    (hOriginal : Structure.IsOriginalPartialHomomorphism
      D.toStructure Target.toStructure f)
    (hTagged : IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts) C
      (genuineWithPartsTagged2019
        Target.toStructure.toNonemptyPartial Target.part) f)
    (hExactLift :
      ∀ {T : Type w} [Finite T]
        (E : Structure L T) (_hIrred : E.Irreducible)
        (e : Structure.Embedding E D.toStructure),
        ∃ j : RelStructure.Embedding
          (genuineWithPartsTagged2019
            E.toNonemptyPartial (D.part ∘ e.toFun)) C,
          IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts)
            (genuineWithPartsTagged2019
              E.toNonemptyPartial (D.part ∘ e.toFun)) ∧
          ∀ x : T, j x = e.toFun x) :
    Structure.IsOriginalPartialHomomorphismEmbedding
      D.toStructure Target.toStructure f := by
  classical
  refine ⟨hOriginal, ?_⟩
  intro T E hIrred e
  letI : Finite T := Finite.of_injective e.toFun e.injective
  obtain ⟨j, hUIrred, hj⟩ := hExactLift E hIrred e
  have hTransD :
      FibreTransversal D.toStructure.toNonemptyPartial D.part :=
    (nativeFunctionFibreTransversal_iff_partial
      D.toStructure D.part).mp D.funcTransversal
  have hTransTarget :
      FibreTransversal Target.toStructure.toNonemptyPartial Target.part :=
    (nativeFunctionFibreTransversal_iff_partial
      Target.toStructure Target.part).mp Target.funcTransversal
  have hTransE :
      FibreTransversal E.toNonemptyPartial (D.part ∘ e.toFun) :=
    fibreTransversal_pullback_fullEmbedding
      E.toNonemptyPartial D.toStructure.toNonemptyPartial
      e.toNonemptyPartial D.part hTransD
  obtain ⟨g, hg⟩ := genuine2019_global_protected_canonical_copy
    C Target.toStructure.toNonemptyPartial Target.part hTransTarget
    f hTagged E.toNonemptyPartial (D.part ∘ e.toFun)
    hTransE hUIrred j
  refine ⟨partialFullEmbedding_toNative g.1, ?_⟩
  intro x
  exact (hg x).trans (congrArg f (hj x))

end AllThoseRamseyClasses.Published
