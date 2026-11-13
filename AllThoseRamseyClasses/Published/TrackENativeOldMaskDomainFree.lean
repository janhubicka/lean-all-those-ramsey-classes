import PartiteConstruction.Functional.NativeWholeWeakFreeAmalgam
import PartiteConstruction.Functional.NativePatternGraphFreeAmalgam2019
import PartiteConstruction.Structure.PartialSetFunctionsWholeMaskPatterns

/-!
# Track E2: actual native free attachments localize complete OLD mask domains

A genuinely native FULL set-valued functional free amalgam preserves
the independent whole-value domain when translated faithfully to
Option(Set). Every active original OLD complete-output mask input root
has its primitive input tuple on one full side. The equality-pattern
argument map is surjective, so ALL distinct input-root vertices also
lie in that side.

The whole original function value is then EXACTLY the image of the
side's entire value set under the full embedding, and the vertex
parts are preserved. Consequently the chosen active output-part
mask has exactly the same set of labels on the side.

This lemma works with repeated primitive inputs, nullary functions,
genuinely multivalued fibres and arbitrary carrier sets. It does not
change the weak source vertices, convert a source-defined projection
into a full map, or assume separate strict target-tree completions.

This is the active-domain half of the native -> original complete-mask
relational free-amalgamation bridge. A separate complete-output-tuple
localization is still needed before the actual OLD tagged component is
proved free; the positive singleton split component is already handled
by pinned IsFreeAmalgam.splitOutputParts_of_partite.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open StructuralRamsey.FunctionalPartite

universe u v w

variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {H E F C : Type w}

/-- One FULL part-preserving embedding has the exact image-of-parts
law on EVERY set of source outputs, not just a selected value. -/
private theorem image_parts_of_full_partite
    {X Y : Type w}
    {Source : FunctionalPartite.System L Parts X}
    {Whole : FunctionalPartite.System L Parts Y}
    (e : FunctionalPartite.Embedding Source Whole)
    (U : Set X) :
    Whole.part '' (Structure.imageSet e.toEmbedding.toFun U) =
      Source.part '' U := by
  ext q
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, hz⟩
    exact ⟨x, hx, (e.map_part x).symm.trans hz⟩
  · rintro ⟨x, hx, hq⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, (e.map_part x).trans hq⟩

/-- If a complete OLD root's original primitive input tuple lies
on a FULL native side and is defined there, then the ENTIRE
complete output-PART mask descends to that side. The distinct
input-root enumeration factors through the same embedding.

The side root is not a closure hull; its vertices are drawn only
from the displayed original input tuple. -/
private theorem originalMaskDomain_factorFullSide
    {X Y : Type w}
    {Source : FunctionalPartite.System L Parts X}
    {Whole : FunctionalPartite.System L Parts Y}
    (e : FunctionalPartite.Embedding Source Whole)
    (p : Language.FunctionInputPattern L)
    (q : Language.CompleteOutputParts Parts)
    (root : Fin p.rootSize → Y)
    (hRootInj : Function.Injective root)
    (U : Set Y)
    (hWholeValue : Whole.toStructure.toNonemptyPartial.func
      p.symbol (root ∘ p.argMap) = some U)
    (hMask : Whole.part '' U = Set.range q.label)
    (args : Fin (L.funcArity p.symbol) → X)
    (hSideDefined : Source.toStructure.toNonemptyPartial.Defined
      p.symbol args)
    (hArgs : root ∘ p.argMap = e.toEmbedding.toFun ∘ args) :
    ∃ (r : Fin p.rootSize → X),
      (Source.toStructure.toNonemptyPartial.wholeMaskPatternGraph
        Source.part).rel (.inr (.inl (p, q))) r ∧
      root = e.toEmbedding.toFun ∘ r := by
  classical
  obtain ⟨r, hRoot, hSourceArgs⟩ :=
    Structure.surjectiveInputRoot_factor
      e.toEmbedding.toFun e.toEmbedding.injective
      p.argMap p.onto root args hArgs
  obtain ⟨T, hT⟩ := hSideDefined
  have hSrcValue : Source.toStructure.toNonemptyPartial.func
      p.symbol (r ∘ p.argMap) = some T := by
    rw [← hSourceArgs]
    exact hT
  have hMap := (e.toEmbedding.toNonemptyPartial).map_func
      p.symbol args
  rw [hT] at hMap
  have hMap' :
      some (Structure.imageSet e.toEmbedding.toFun T) =
        Whole.toStructure.toNonemptyPartial.func
          p.symbol (e.toEmbedding.toFun ∘ args) := hMap
  have hWhole' :
      Whole.toStructure.toNonemptyPartial.func
        p.symbol (e.toEmbedding.toFun ∘ args) = some U := by
    rw [← hArgs]
    exact hWholeValue
  have hImage : Structure.imageSet e.toEmbedding.toFun T = U :=
    Option.some.inj (hMap'.trans hWhole')
  have hPart :
      Source.part '' T = Set.range q.label := by
    calc
      Source.part '' T =
          Whole.part '' (Structure.imageSet e.toEmbedding.toFun T) :=
        (image_parts_of_full_partite e T).symm
      _ = Whole.part '' U := by rw [hImage]
      _ = Set.range q.label := hMask
  have hInj : Function.Injective r := by
    intro a b hab
    apply hRootInj
    calc
      root a = e (r a) := congrFun hRoot a
      _ = e (r b) := congrArg e hab
      _ = root b := (congrFun hRoot b).symm
  refine ⟨r, ?_, hRoot⟩
  change Function.Injective r ∧
    ∃ T : Set X, Source.toStructure.toNonemptyPartial.func
      p.symbol (r ∘ p.argMap) = some T ∧
      Source.part '' T = Set.range q.label
  exact ⟨hInj, T, hSrcValue, hPart⟩

/-- Every canonical ORIGINAL complete-value active OLD mask of a
TRUE native FULL functional free amalgam belongs to one full
part-preserving side, on the SAME complete set of output parts.

This is exactly the domain-relation case of the desired
original OLD mask graph free-amalgamation theorem. It does not
assert the complete-output tuple case or the final E2 Ramsey
control. The argument uses faithful Option(Set) domain freeness,
not a clipped weak-fibre homomorphism. -/
theorem nativeFreeAmalgam_originalWholeMaskDomain_side
    {Root : FunctionalPartite.System L Parts H}
    {Left : FunctionalPartite.System L Parts E}
    {Right : FunctionalPartite.System L Parts F}
    {Whole : FunctionalPartite.System L Parts C}
    {sL : FunctionalPartite.Embedding Root Left}
    {sR : FunctionalPartite.Embedding Root Right}
    {iL : FunctionalPartite.Embedding Left Whole}
    {iR : FunctionalPartite.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam
      sL.toEmbedding sR.toEmbedding
      iL.toEmbedding iR.toEmbedding)
    (p : Language.FunctionInputPattern L)
    (q : Language.CompleteOutputParts Parts)
    (root : Fin p.rootSize → C)
    (hDomain :
      (Whole.toStructure.toNonemptyPartial.wholeMaskPatternGraph
        Whole.part).rel (.inr (.inl (p, q))) root) :
    (∃ r : Fin p.rootSize → E,
      (Left.toStructure.toNonemptyPartial.wholeMaskPatternGraph
        Left.part).rel (.inr (.inl (p, q))) r ∧
      root = iL.toEmbedding.toFun ∘ r) ∨
    (∃ r : Fin p.rootSize → F,
      (Right.toStructure.toNonemptyPartial.wholeMaskPatternGraph
        Right.part).rel (.inr (.inl (p, q))) r ∧
      root = iR.toEmbedding.toFun ∘ r) := by
  classical
  have hFreePartial : PartialSetStructure.IsFreeAmalgam
      sL.toEmbedding.toNonemptyPartial
      sR.toEmbedding.toNonemptyPartial
      iL.toEmbedding.toNonemptyPartial
      iR.toEmbedding.toNonemptyPartial :=
    hFree.toNonemptyPartial
  change Function.Injective root ∧
    ∃ U : Set C,
      Whole.toStructure.toNonemptyPartial.func
        p.symbol (root ∘ p.argMap) = some U ∧
      Whole.part '' U = Set.range q.label at hDomain
  obtain ⟨hRootInj, U, hWholeValue, hMask⟩ := hDomain
  have hWholeDefined :
      Whole.toStructure.toNonemptyPartial.Defined
        p.symbol (root ∘ p.argMap) := ⟨U, hWholeValue⟩
  rcases (hFreePartial.defined_iff
      p.symbol (root ∘ p.argMap)).mp hWholeDefined with
      ⟨args, hSideDefined, hArgs⟩ |
      ⟨args, hSideDefined, hArgs⟩
  · exact Or.inl <|
      originalMaskDomain_factorFullSide iL
        p q root hRootInj U hWholeValue hMask
        args hSideDefined hArgs
  · exact Or.inr <|
      originalMaskDomain_factorFullSide iR
        p q root hRootInj U hWholeValue hMask
        args hSideDefined hArgs

end AllThoseRamseyClasses.Published
