import AllThoseRamseyClasses.Published.TrackEOldSplitHybridCanonical
import PartiteConstruction.Functional.WholeMaskClosureSemiClosed2019
import PartiteConstruction.Functional.NativePatternGraphFreeAmalgam2019
import PartiteConstruction.Iterated.LocalTreeLike

/-!
# Track E2: combine two genuine component free-amalgam diagrams in one base hybrid

The exact native split/mask hybrid signature stores two independently
existing canonical tagged relational encodings of the SAME genuine
functional partite System, plus unary predicates naming EVERY part.

This theorem supplies a precise composition rule: when a single
diagram of full part-preserving native System embeddings gives a
relational free amalgam in BOTH the original complete-mask tagged
component and the positive singleton-split pattern-tagged component,
its canonical BASE HYBRID representations form a free amalgam on the
identical carriers and maps. The unary part predicates are harmless:
each is a one-coordinate relation, and full embeddings preserve parts.

The proof is relation-by-relation, retaining the actual OLD domain
masks, positive split incidences and source-overlap exactly. It does
not assume separate free diagrams can be glued along unrelated
vertex maps; all four maps are the SAME native embeddings in both.

This is an honest CONDITIONAL source assembly lemma. Still needed
are a native full-free-amalgam -> original complete-mask component
free-amalgam bridge and a compatible component-normalization theorem
for arbitrary constrained relational hybrid pictures. Joint full-root
tagging of the resulting base hybrid free diagram is a separate
verified/proposed functor (#1075). No strict target-tree completion,
strong AP of K, or E2 Ramsey conclusion follows here.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The SAME native full partite embedding seen in the canonical
old complete-mask/full-root tagged component. This reflects both
complete values and persistent active domains, not just positivity. -/
noncomputable def systemEmbedding_oldMaskTagged
    {VA VB : Type w}
    {A : FunctionalPartite.System L Parts VA}
    {B : FunctionalPartite.System L Parts VB}
    (e : FunctionalPartite.Embedding A B) :
    RelStructure.Embedding
      (wholeMaskTagExpansion
        (A.toStructure.toNonemptyPartial.wholeMaskPatternGraph A.part))
      (wholeMaskTagExpansion
        (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part)) :=
  (e.toEmbedding.toNonemptyPartial.wholeMaskPatternGraph
    A.part B.part e.map_part).wholeMaskTag

/-- The same native embedding seen in the positive
singleton-output-part equality-pattern/full-root tagged component. -/
noncomputable def systemEmbedding_splitPatternTagged
    {VA VB : Type w}
    {A : FunctionalPartite.System L Parts VA}
    {B : FunctionalPartite.System L Parts VB}
    (e : FunctionalPartite.Embedding A B) :
    RelStructure.Embedding
      (patternTagExpansion
        A.splitOutputParts.toStructure.patternGraph)
      (patternTagExpansion
        B.splitOutputParts.toStructure.patternGraph) :=
  (e.splitOutputParts.toEmbedding.patternGraph).patternTag

/-- If the SAME four genuine native partite maps already give
free amalgam diagrams in both canonical tagged function encodings,
their complete base split/mask hybrid representations form a
genuine relational free amalgam as well.

The original full-root tags, split incidence tags and isolated-vertex
part predicates are kept. This does not construct either component
free-amalgam diagram, so is a compositional SOURCE result rather than
a class-closure/strong-AP theorem. -/
theorem baseHybrid_freeAmalgam_of_componentFree
    {VH VE VF VC : Type w}
    {Root : FunctionalPartite.System L Parts VH}
    {Left : FunctionalPartite.System L Parts VE}
    {Right : FunctionalPartite.System L Parts VF}
    {Whole : FunctionalPartite.System L Parts VC}
    (sL : FunctionalPartite.Embedding Root Left)
    (sR : FunctionalPartite.Embedding Root Right)
    (iL : FunctionalPartite.Embedding Left Whole)
    (iR : FunctionalPartite.Embedding Right Whole)
    (hOld : RelStructure.IsFreeAmalgam
      (systemEmbedding_oldMaskTagged sL)
      (systemEmbedding_oldMaskTagged sR)
      (systemEmbedding_oldMaskTagged iL)
      (systemEmbedding_oldMaskTagged iR))
    (hSplit : RelStructure.IsFreeAmalgam
      (systemEmbedding_splitPatternTagged sL)
      (systemEmbedding_splitPatternTagged sR)
      (systemEmbedding_splitPatternTagged iL)
      (systemEmbedding_splitPatternTagged iR)) :
    RelStructure.IsFreeAmalgam
      (systemEmbedding_splitMaskHybrid sL)
      (systemEmbedding_splitMaskHybrid sR)
      (systemEmbedding_splitMaskHybrid iL)
      (systemEmbedding_splitMaskHybrid iR) := by
  classical
  refine {
    covers := hOld.covers
    overlap := hOld.overlap
    rel_iff := ?_
  }
  intro R t
  rcases R with R | R
  · exact hOld.rel_iff R t
  · rcases R with R | q
    · exact hSplit.rel_iff R t
    · change
        (Whole.part (t (0 : Fin 1)) = q) ↔
          (∃ x : Fin 1 → VE,
            Left.part (x (0 : Fin 1)) = q ∧
              t = iL ∘ x) ∨
          (∃ x : Fin 1 → VF,
            Right.part (x (0 : Fin 1)) = q ∧
              t = iR ∘ x)
      constructor
      · intro hq
        rcases hOld.covers (t (0 : Fin 1)) with
            ⟨a, ha⟩ | ⟨b, hb⟩
        · refine Or.inl ⟨(fun _ : Fin 1 => a), ?_, ?_⟩
          · calc
              Left.part a = Whole.part (iL a) :=
                (iL.map_part a).symm
              _ = Whole.part (t (0 : Fin 1)) :=
                congrArg Whole.part ha.symm
              _ = q := hq
          · funext k
            have hk : k = (0 : Fin 1) := by
              change (k : Fin 1) = (0 : Fin 1)
              exact Subsingleton.elim _ _
            subst k
            exact ha
        · refine Or.inr ⟨(fun _ : Fin 1 => b), ?_, ?_⟩
          · calc
              Right.part b = Whole.part (iR b) :=
                (iR.map_part b).symm
              _ = Whole.part (t (0 : Fin 1)) :=
                congrArg Whole.part hb.symm
              _ = q := hq
          · funext k
            have hk : k = (0 : Fin 1) := by
              change (k : Fin 1) = (0 : Fin 1)
              exact Subsingleton.elim _ _
            subst k
            exact hb
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact (iL.map_part (x (0 : Fin 1))).trans hx
        · exact (iR.map_part (x (0 : Fin 1))).trans hx

end AllThoseRamseyClasses.Published
