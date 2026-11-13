import AllThoseRamseyClasses.Published.TrackEJointHybridFreeAmalgam
import AllThoseRamseyClasses.Published.TrackEJointHybridExactInduce

/-!
# Track E2: EXACT joint full-hybrid-root tag semantics is weak-hereditary and free-stable

The combined 2019 hybrid relational signature has a BASE language
(original complete OLD masks, split per-part incidences, unary
vertex-part predicates) plus TWO FRESH full-hybrid-root tagged
relation families. On a CANONICAL expansion the fresh tag has
exactly its intended meaning: a positive corresponding base
output tuple together with a FULL embedding of the named entire
HYBRID input root, with every root vertex displayed in the tuple.

An arbitrary relational structure in the joint language need not
satisfy this semantic equivalence. U-CLOSEDNESS alone describes
unique closure tuples over roots; it does not say that every extra
base-positive output tuple carries its correct fresh tag.

We name this independent normality law HasExactJointRootTags:
  C = splitMaskJointRootExpansion (splitMaskJointRootReduct C).

It is true for every canonical source, inherited on EVERY exact
induced weak vertex set, and stable under any true relational
free amalgam whose two sides have exact tag semantics. The proof
of free stability projects the actual FULL free diagram to its
BASE hybrid reduct; the already validated full-root tagging
free-amalgamation theorem builds a second free diagram from it.
Both diagrams have identical vertices, side maps, and side
relations by the hypothesis. Their free relation clauses force
the same whole relations, hence the same joint tagged structure.

This is a genuinely useful target-side PROFILE/TAG semantic
invariant, but it does NOT normalize arbitrary base OLD mask
domains, original complete values, split per-part singleton
outputs, or cross-incidence target conflicts. It does not assert
a sparse Ramsey construction or full H-relative local completion.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Every fresh full-hybrid-root tag in C is EXACTLY the canonical
full-root relation computed from the BASE hybrid reduct of C,
with no omitted tags or extra spurious tagged tuples. -/
def HasExactJointRootTags
    {V : Type w}
    (C : RelStructure (L.splitMaskJointRootLanguage Parts) V) : Prop :=
  C = splitMaskJointRootExpansion (splitMaskJointRootReduct C)

/-- A truly canonical full-hybrid-root expansion obviously has the
literal intended semantics for BOTH its split and original mask tags. -/
theorem splitMaskJointRootExpansion_hasExactJointRootTags
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) :
    HasExactJointRootTags (splitMaskJointRootExpansion E) := by
  unfold HasExactJointRootTags
  rw [splitMaskJointRoot_reduct_canonical]

/-- Tag semantic exactness is hereditary to EVERY induced weak
subset S, without normalizing/recomputing any original OLD domain
bit from its clipped native weak-function values. -/
theorem HasExactJointRootTags.induce
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (h : HasExactJointRootTags C) (S : Set V) :
    HasExactJointRootTags (C.induce S) := by
  unfold HasExactJointRootTags at h ⊢
  calc
    C.induce S =
        (splitMaskJointRootExpansion
          (splitMaskJointRootReduct C)).induce S :=
      congrArg (fun T => T.induce S) h
    _ = splitMaskJointRootExpansion
          ((splitMaskJointRootReduct C).induce S) :=
      (splitMaskJointRootExpansion_induce_eq
        (splitMaskJointRootReduct C) S).symm
    _ = splitMaskJointRootExpansion
          (splitMaskJointRootReduct (C.induce S)) := rfl

namespace IsFreeAmalgam

/-- Forgetting fresh JOINT full-root tags of an arbitrary TRUE
relational free-amalgamation diagram preserves all three defining
free-amalgam clauses, on exactly the same side/root vertices. -/
theorem splitMaskJointRootReduct
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskJointRootLanguage Parts) H}
    {Left : RelStructure (L.splitMaskJointRootLanguage Parts) E}
    {Right : RelStructure (L.splitMaskJointRootLanguage Parts) F}
    {Whole : RelStructure (L.splitMaskJointRootLanguage Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) :
    IsFreeAmalgam
      sL.splitMaskJointRootReduct sR.splitMaskJointRootReduct
      iL.splitMaskJointRootReduct iR.splitMaskJointRootReduct where
  covers := hFree.covers
  overlap := hFree.overlap
  rel_iff R xs := hFree.rel_iff (.inl R) xs

end IsFreeAmalgam

/-- Both sides have exact tag semantics, and the diagram is a
TRUE FULL free amalgam of the JOINT relational language. Then
the whole structure also has EXACT semantic tag expansion.
The root's exact-tag hypothesis is not separately required:
full induced side embeddings already constrain its root profile.

This is NOT output-value/mask coherence of the base hybrid target. -/
theorem HasExactJointRootTags.freeAmalgam
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskJointRootLanguage Parts) H}
    {Left : RelStructure (L.splitMaskJointRootLanguage Parts) E}
    {Right : RelStructure (L.splitMaskJointRootLanguage Parts) F}
    {Whole : RelStructure (L.splitMaskJointRootLanguage Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hLeft : HasExactJointRootTags Left)
    (hRight : HasExactJointRootTags Right) :
    HasExactJointRootTags Whole := by
  classical
  have hBase : IsFreeAmalgam
      sL.splitMaskJointRootReduct sR.splitMaskJointRootReduct
      iL.splitMaskJointRootReduct iR.splitMaskJointRootReduct :=
    hFree.splitMaskJointRootReduct
  have hTagged := hBase.splitMaskJointRoot
  unfold HasExactJointRootTags at hLeft hRight ⊢
  apply RelStructure.rel_injective
  funext R z
  apply propext
  calc
    Whole.rel R z ↔
        (∃ x : Fin ((L.splitMaskJointRootLanguage Parts).arity R) → E,
          Left.rel R x ∧ z = iL ∘ x) ∨
        (∃ y : Fin ((L.splitMaskJointRootLanguage Parts).arity R) → F,
          Right.rel R y ∧ z = iR ∘ y) :=
      hFree.rel_iff R z
    _ ↔
        (∃ x : Fin ((L.splitMaskJointRootLanguage Parts).arity R) → E,
          (splitMaskJointRootExpansion
            (splitMaskJointRootReduct Left)).rel R x ∧ z = iL ∘ x) ∨
        (∃ y : Fin ((L.splitMaskJointRootLanguage Parts).arity R) → F,
          (splitMaskJointRootExpansion
            (splitMaskJointRootReduct Right)).rel R y ∧ z = iR ∘ y) := by
      rw [← hLeft, ← hRight]
    _ ↔
        (splitMaskJointRootExpansion
          (splitMaskJointRootReduct Whole)).rel R z :=
      (hTagged.rel_iff R z).symm

end StructuralRamsey.RelStructure
