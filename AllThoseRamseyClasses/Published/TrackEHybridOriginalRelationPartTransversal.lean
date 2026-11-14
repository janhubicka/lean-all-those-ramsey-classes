import AllThoseRamseyClasses.Published.TrackEOldSplitHybridCanonical
import PartiteConstruction.Iterated.LocalTreeLike

/-!
# Track E2: primitive relational tuples respect the hybrid unary parts

The hybrid target-normality predicate enforces a unique vertex-part
label, even for isolated vertices, and correct labels for positive
function outputs. It does NOT by itself force a primitive
RELATIONAL tuple to have distinct parts at distinct vertices.

That is a separate semantic condition for decoding arbitrary
hybrid relational Pictures to a genuine native
`FunctionalPartite.System`: whenever a displayed ORIGINAL
primitive relational tuple has two coordinates of the same
unary-labelled part, those two vertices must be equal.

We isolate the invariant without making any arbitrary-target
decoder claims, then prove it for canonical native partite
sources, exact induced weak tests, and all TRUE FULL relational
free amalgams. The free-amalgam proof localizes each original
relation tuple to a FULL side and reflects both unary labels
through that side embedding. The resulting equality is
transported back into the amalgam on the SAME vertex map.

This law is independent of complete OLD mask coherence,
positive split-output transport, joint U-closedness and the
yet-unproven two-pass finite-family ordered sparse Ramsey
construction. No vertex is added and no output is completed.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Original relation tuples are part-transversal in the native
sense: two coordinates with the same positive unary PART
predicate must name the same vertex. The equivalence to a
part-map formulation uses the independently maintained
`HybridUniqueVertexPart` predicate. -/
def HybridOriginalRelationPartTransversal
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  ∀ (R : L.RelSymbol)
    (t : Fin (L.relArity R) → V),
    E.rel (.inl (.inl (.inl R))) t →
    ∀ (i j : Fin (L.relArity R)) (q : Parts),
      E.rel (.inr (.inr q)) (fun _ : Fin 1 => t i) →
      E.rel (.inr (.inr q)) (fun _ : Fin 1 => t j) →
      t i = t j

/-- The canonical relational part of a native functional partite
System is transversal, with the same original part map. -/
theorem canonicalHybrid_originalRelationPartTransversal
    {V : Type w}
    (A : FunctionalPartite.System L Parts V) :
    HybridOriginalRelationPartTransversal A.splitMaskHybrid := by
  intro R t hRel i j q hPartI hPartJ
  have hOriginal : A.rel R t := hRel
  have hi : A.part (t i) = q := hPartI
  have hj : A.part (t j) = q := hPartJ
  exact A.relTransversal R t hOriginal i j (hi.trans hj.symm)

/-- Literal weak-induced vertex sets retain the relation/
unary-part collision guard, even when the induced subset is
not function-closed or joint-U-closed. -/
theorem HybridOriginalRelationPartTransversal.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridOriginalRelationPartTransversal E)
    (S : Set V) :
    HybridOriginalRelationPartTransversal (E.induce S) := by
  intro R t hRel i j q hPartI hPartJ
  apply Subtype.ext
  exact h R (Subtype.val ∘ t) hRel i j q hPartI hPartJ

/-- Reflect a positive unary part predicate through a FULL
hybrid relational embedding. A side's part label remains
visible and is not an exterior amalgam vertex. -/
private theorem reflect_originalPartLabel
    {X Y : Type w}
    {Side : RelStructure (L.splitMaskHybrid Parts) X}
    {Whole : RelStructure (L.splitMaskHybrid Parts) Y}
    (e : Embedding Side Whole) (q : Parts) (x : X)
    (h : Whole.rel (.inr (.inr q))
      (fun _ : Fin 1 => e x)) :
    Side.rel (.inr (.inr q))
      (fun _ : Fin 1 => x) := by
  apply (e.map_rel_iff (.inr (.inr q))
    (fun _ : Fin 1 => x)).mp
  simpa only [Function.comp_apply] using h

/-- An entire primitive ORIGINAL relational tuple that comes
from one FULL side retains the relation/part collision law
in the whole, including all its displayed unary part labels. -/
private theorem originalRelationPartTransversal_fromSide
    {X Y : Type w}
    {Side : RelStructure (L.splitMaskHybrid Parts) X}
    {Whole : RelStructure (L.splitMaskHybrid Parts) Y}
    (e : Embedding Side Whole)
    (hSide : HybridOriginalRelationPartTransversal Side)
    (R : L.RelSymbol)
    (t : Fin (L.relArity R) → Y)
    (x : Fin (L.relArity R) → X)
    (hx : Side.rel (.inl (.inl (.inl R))) x)
    (ht : t = e ∘ x)
    (i j : Fin (L.relArity R))
    (q : Parts)
    (hi : Whole.rel (.inr (.inr q))
      (fun _ : Fin 1 => t i))
    (hj : Whole.rel (.inr (.inr q))
      (fun _ : Fin 1 => t j)) :
    t i = t j := by
  have hUi : Whole.rel (.inr (.inr q))
      (fun _ : Fin 1 => e (x i)) := by
    have hti : t i = e (x i) := congrFun ht i
    simpa only [hti] using hi
  have hUj : Whole.rel (.inr (.inr q))
      (fun _ : Fin 1 => e (x j)) := by
    have htj : t j = e (x j) := congrFun ht j
    simpa only [htj] using hj
  have hSideEq : x i = x j :=
    hSide R x hx i j q
      (reflect_originalPartLabel e q (x i) hUi)
      (reflect_originalPartLabel e q (x j) hUj)
  calc
    t i = e (x i) := congrFun ht i
    _ = e (x j) := congrArg e hSideEq
    _ = t j := (congrFun ht j).symm

/-- The original relation/part collision guard survives EVERY
TRUE FULL relational free amalgam, with no U-closed overlap or
positive-arity premise: each actual primitive relation tuple
comes entirely from one side, and the unary labels reflect
through that same FULL embedding. -/
theorem HybridOriginalRelationPartTransversal.freeAmalgam
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hLeft : HybridOriginalRelationPartTransversal Left)
    (hRight : HybridOriginalRelationPartTransversal Right) :
    HybridOriginalRelationPartTransversal Whole := by
  intro R t hRel i j q hi hj
  rcases (hFree.rel_iff (.inl (.inl (.inl R))) t).mp
      hRel with
    ⟨x, hx, htx⟩ | ⟨y, hy, hty⟩
  · exact originalRelationPartTransversal_fromSide
      iL hLeft R t x hx htx i j q hi hj
  · exact originalRelationPartTransversal_fromSide
      iR hRight R t y hy hty i j q hi hj

end StructuralRamsey.RelStructure
