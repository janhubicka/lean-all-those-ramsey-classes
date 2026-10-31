import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Functional.WholeMaskCanonicalClosedInduce2019
import PartiteConstruction.Functional.WholeMaskPartPreservingEmbeddingEquiv2019

/-!
# Corrected 2019 ambient-relative local maps on genuinely CLOSED weak tests

The intrinsic whole-fibre weak functional restriction and the EXACT
ambient-induced OLD tagged relational test coincide when the chosen
subset S is function-closed. Consequently every FULL part-preserving
genuine partial-function embedding of the induced CLOSED substructure
into a transversal functional target canonically yields a corrected
induced-closed U-homomorphism-embedding from the EXACT ambient induced
tagged OLD test into that canonical target.

This identifies a POSITIVE case of the remaining functional local
K-completion bridge. For arbitrary unclosed S the statement cannot
be made: the ambient OLD domain masks persist even where the genuine
weak partial application has become undefined (verified unary example
PRs #524 and #530). The 2019 small-test local axiom tests ALL S, so
this positive lemma alone does not prove it.

Neither the weak source S nor its target map is altered or enlarged.
Defined-empty stays distinct from undefined. No assumptions about
the arbitrary K-class are made.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V W : Type w}

/-- Exact closed weak input carrier: an original full functional
embedding canonically yields a corrected 2019 induced-closed map
from the ambient tagged OLD source, with the SAME vertex mapping. -/
theorem genuine2019_closedWeak_fullEmbedding_to_relativeMap
    (A : PartialSetStructure L V)
    (partA : V → Parts)
    (S : Set V) (hClosedS : A.IsClosed S)
    (Target : PartialSetStructure L W)
    (partTarget : W → Parts)
    (e : PartPreservingEmbedding
      (A.induceClosed S hClosedS) (partA ∘ Subtype.val)
      Target partTarget) :
    IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      ((wholeMaskTagExpansion (withPartsWholeMaskOld A partA)).induce S)
      (wholeMaskTagExpansion (withPartsWholeMaskOld Target partTarget))
      e.1.toFun := by
  classical
  let partS : S → Parts := partA ∘ Subtype.val
  let inclusionPlus : PartialSetStructure.Embedding
      ((A.induceClosed S hClosedS).withParts partS)
      (A.withParts partA) :=
    (A.closedInclusion S hClosedS).withParts partS partA
      (fun _ => rfl)
  let inclusionOld : RelStructure.Embedding
      (withPartsWholeMaskOld (A.induceClosed S hClosedS) partS)
      (withPartsWholeMaskOld A partA) :=
    inclusionPlus.wholeMaskPatternGraph partS partA
      (fun _ => rfl)
  have hOldEq :
      withPartsWholeMaskOld (A.induceClosed S hClosedS) partS =
        (withPartsWholeMaskOld A partA).induce S := by
    apply RelStructure.rel_injective
    funext R xs
    have hRel := inclusionOld.map_rel_iff R xs
    change (withPartsWholeMaskOld A partA).rel R
        (Subtype.val ∘ xs) ↔
      (withPartsWholeMaskOld (A.induceClosed S hClosedS) partS).rel
        R xs at hRel
    exact propext hRel.symm
  have hTagEq :
      wholeMaskTagExpansion
        (withPartsWholeMaskOld (A.induceClosed S hClosedS)
          (partA ∘ Subtype.val)) =
      (wholeMaskTagExpansion (withPartsWholeMaskOld A partA)).induce S := by
    calc
      wholeMaskTagExpansion
          (withPartsWholeMaskOld (A.induceClosed S hClosedS) partS) =
        wholeMaskTagExpansion ((withPartsWholeMaskOld A partA).induce S) := by
          rw [hOldEq]
      _ = (wholeMaskTagExpansion (withPartsWholeMaskOld A partA)).induce S :=
        wholeMaskTagExpansion_induce_eq (withPartsWholeMaskOld A partA) S
  let eTagged := (PartPreservingEmbedding.encode e).wholeMaskTag
  let eOld : RelStructure.Embedding
      ((wholeMaskTagExpansion (withPartsWholeMaskOld A partA)).induce S)
      (wholeMaskTagExpansion (withPartsWholeMaskOld Target partTarget)) := {
    toFun := e.1.toFun
    injective := e.1.injective
    map_rel_iff := by
      intro R xs
      have hMap := eTagged.map_rel_iff R xs
      change
        (wholeMaskTagExpansion (withPartsWholeMaskOld Target partTarget)).rel
          R (e.1.toFun ∘ xs) ↔
        (wholeMaskTagExpansion
          (withPartsWholeMaskOld (A.induceClosed S hClosedS) partS)).rel
          R xs at hMap
      rw [hTagEq] at hMap
      exact hMap
  }
  have hMap : IsClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      ((wholeMaskTagExpansion (withPartsWholeMaskOld A partA)).induce S)
      (wholeMaskTagExpansion (withPartsWholeMaskOld Target partTarget))
      e.1.toFun :=
    eOld.isClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
  exact IsClosedUHomomorphismEmbedding.toInducedClosed hMap

end AllThoseRamseyClasses.Published
