import AllThoseRamseyClasses.Published.TrackEHybridExactReencodeStrongAmalgam
import AllThoseRamseyClasses.Published.TrackEHybridInnerTagNormality

/-!
# Track E2: componentwise exact native re-encoding implies full JOINT equality

The full joint hybrid representation has three actual base
components, plus the fresh outer JOINT full-root tags:

(1) the original complete OLD mask/whole-output tagged structure;
(2) the per-output-part singleton PATTERN tagged structure;
(3) one unary output-part predicate for every vertex.

The strengthened target-normality predicate
`HybridJointExactReencodeNormal` already reconstructs a genuine
native functional partite System A on EXACTLY the same vertex
carrier, and it contains exact semantics of the outer JOINT
tag families. It also specifies a UNIQUE unary part predicate
on every vertex, including isolated ones.

The remaining exact target-re-encoding work can therefore be
reduced to TWO component equalities:
* the existing original OLD nested tagged component equals the
  canonical whole-mask tagging of A's faithful native partial
  function encoding;
* the existing singleton split nested tagged component equals
  the canonical pattern tagging of A.splitOutputParts.

This module proves the GLUING theorem: those two equalities
imply literal equality of the ENTIRE actual JOINT-tagged
relational structure C with the canonical JOINT re-encoding
of its own reconstructed native System A, on identical
vertices, relations, function values and all three tag layers.
No embedding or isomorphism is substituted for equality.

The unary component requires no new hypothesis: exact unique
part labels and A.part = the recovered literal partMap
already establish its equality, including isolated vertices.
The outer JOINT layer follows immediately from the existing
`HasExactJointRootTags` equality and congruence of the
canonical expansion functor on the base structure.

This is a precise compositional theorem, NOT yet an
unconditional full re-encoding statement for all normal
Pictures: the two component equalities are explicit premises.
Separate modules seek to discharge them via exact OLD domain/
value reconstruction, split domain/positive-incidence
correspondence, and exact INNER tag semantics. The two-pass
finite-family ordered sparse Ramsey theorem remains a
different outstanding obligation.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- EXACT matching of the two nested tagged components of an
actual JOINT hybrid Picture with the canonical tagged source
relations of the reconstructed native partite System.

The unary part predicates and the fresh OUTER JOINT root tags
are not assumed separately here: they are already forced
by the underlying `HybridJointExactReencodeNormal` package. -/
def HybridJointExactReencodeComponents
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (h : HybridJointExactReencodeNormal C) : Prop :=
  hybridOldTaggedReduct (splitMaskJointRootReduct C) =
    wholeMaskTagExpansion
      (h.native.toNativeSystem.toStructure.toNonemptyPartial.wholeMaskPatternGraph
        h.native.toNativeSystem.part) ∧
  hybridSplitTaggedReduct (splitMaskJointRootReduct C) =
    patternTagExpansion
      (h.native.toNativeSystem.splitOutputParts.toStructure.patternGraph)

/-- If the TWO nested tagged component equalities are established,
the ENTIRE actual JOINT hybrid target is LITERALLY the canonical
joint re-encoding of the SAME native partite System.

The proof is extensionality across the OLD, SPLIT and unary
parts of the base hybrid language. Unary labels are identified
by unique vertex-part normality; the full JOINT target equality
then follows from its independently certified exact tag
semantics. No new vertex, output value or tag is introduced. -/
theorem HybridJointExactReencodeNormal.fullJoint_eq_of_components
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (h : HybridJointExactReencodeNormal C)
    (hComponents : HybridJointExactReencodeComponents h) :
    C = splitMaskJointRootExpansion
      h.native.toNativeSystem.splitMaskHybrid := by
  classical
  let Base : RelStructure (L.splitMaskHybrid Parts) V :=
    splitMaskJointRootReduct C
  let A : FunctionalPartite.System L Parts V :=
    h.native.toNativeSystem
  let hParts : HybridUniqueVertexPart Base :=
    h.native.strict.normal.coherent.1.2.2.2
  have hBase : Base = A.splitMaskHybrid := by
    apply RelStructure.rel_injective
    funext R t
    apply propext
    rcases R with R | R
    · have heq :
          (hybridOldTaggedReduct Base).rel R t =
            (wholeMaskTagExpansion
              (A.toStructure.toNonemptyPartial.wholeMaskPatternGraph
                A.part)).rel R t :=
        congrArg
          (fun X : RelStructure (L.wholeMaskTagLanguage Parts) V =>
            X.rel R t) hComponents.1
      exact Iff.of_eq heq
    · rcases R with R | q
      · have heq :
            (hybridSplitTaggedReduct Base).rel R t =
              (patternTagExpansion
                (A.splitOutputParts.toStructure.patternGraph)).rel R t :=
          congrArg
            (fun X : RelStructure
                ((L.outputPartIndexed Parts).patternTag) V =>
              X.rel R t) hComponents.2
        exact Iff.of_eq heq
      · change Base.rel (.inr (.inr q)) t ↔
          A.part (t (0 : Fin 1)) = q
        have hTuple : t =
            (fun _ : Fin 1 => t (0 : Fin 1)) := by
          funext i
          exact congrArg t (Subsingleton.elim i 0)
        constructor
        · intro ht
          rw [hTuple] at ht
          exact hParts.partMap_eq_of_label (t 0) q ht
        · intro hq
          have ht := hParts.partMap_hasLabel (t 0)
          rw [hq] at ht
          rw [hTuple]
          exact ht
  calc
    C = splitMaskJointRootExpansion Base :=
      h.native.strict.normal.exactTags
    _ = splitMaskJointRootExpansion A.splitMaskHybrid :=
      congrArg (fun E : RelStructure (L.splitMaskHybrid Parts) V =>
        splitMaskJointRootExpansion E) hBase

end StructuralRamsey.RelStructure
