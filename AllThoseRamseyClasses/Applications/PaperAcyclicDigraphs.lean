import AllThoseRamseyClasses.Applications.PaperOrderedGraphs
import PartiteConstruction.Ramsey.CopywiseRamseyTransfer

/-!
# Another actual 2019 application: acyclic digraphs with linear extension

Corollary cor:acyclic of the paper. A finite directed graph with
all edges increasing in its distinguished linear order is acyclic,
and every finite DAG admits such an order.

For arbitrary Ramsey witness C in all freely ordered directed graphs,
delete precisely those arcs that do not increase C's vertex order.
The resulting graph is a DAG with this order as linear extension.
The identity C -> C_forward need not preserve all embeddings, but
on every full copy of B (whose edges increase the order) it IS a full
embedding, so the proved B-copywise arrow-transfer theorem applies.

This is a direct proof using the ordinary ordered-relational Ramsey
theorem and avoids reconstructing a weak-transitive closure.
-/

namespace AllThoseRamseyClasses.Applications.PaperGraphs

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The direction of every original edge respects the distinguished
(strict) linear vertex order. -/
def EdgesForward {V : Type} [LinearOrder V]
    (C : RelStructure Lang V) : Prop :=
  ∀ x y : V, edge C x y → x < y

/-- Delete the edges that do not respect the chosen total order. -/
def forwardReduct {V : Type} [LinearOrder V]
    (C : RelStructure Lang V) : RelStructure Lang V where
  rel := fun
    | .edge, t => C.rel .edge t ∧ t 0 < t 1

theorem forwardReduct_edgesForward {V : Type} [LinearOrder V]
    (C : RelStructure Lang V) :
    EdgesForward (forwardReduct C) := by
  intro x y h
  exact h.2

/-- Copies of a directed graph whose edges respect its order survive
the forward-edge deletion as FULL induced ordered embeddings.
No other copies need be preserved. -/
theorem forwardReduct_preserves_ordered_copies
    {V W : Type} [LinearOrder V] [LinearOrder W]
    (B : RelStructure Lang V) (C : RelStructure Lang W)
    (hB : EdgesForward B) :
    CopywiseCompletion B.ordered C.ordered
      (forwardReduct C).ordered (fun w => w) := by
  intro b
  let e : Embedding B.ordered (forwardReduct C).ordered := {
    toFun := b
    injective := b.injective
    map_rel_iff := by
      intro R t
      cases R with
      | inl s =>
          cases s with
          | edge =>
              change (C.rel .edge (b ∘ t) ∧ b (t 0) < b (t 1)) ↔
                B.rel .edge t
              constructor
              · intro h
                exact (b.map_rel_iff (.inl .edge) t).mp h.1
              · intro h
                refine ⟨(b.map_rel_iff (.inl .edge) t).mpr h, ?_⟩
                exact b.strictMono (hB (t 0) (t 1) h)
      | inr u =>
          cases u
          exact b.map_rel_iff (.inr ()) t
  }
  exact ⟨e, fun _ => rfl⟩

/-- The 2019 paper's acyclic-digraph-with-linear-extension Ramsey
corollary, represented by the equivalent external strict order.
The finite Ramsey target itself has all edges forward, not merely
an acyclic reduct. -/
theorem freelyOrderedAcyclicDigraphs_areRamsey
    {U V : Type} [Finite U] [Finite V]
    [LinearOrder U] [LinearOrder V]
    (A : RelStructure Lang U) (B : RelStructure Lang V)
    (_hA : EdgesForward A) (hB : EdgesForward B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type) (_ : Finite W) (o : LinearOrder W)
      (C : RelStructure Lang W),
      @EdgesForward W o C ∧
      StructuralRamsey.Arrow A.ordered B.ordered
        (@RelStructure.ordered Lang W C o.toLT) κ := by
  obtain ⟨W,hW,o,C,hRamsey⟩ :=
    freelyOrderedDigraphs_areRamsey A B κ
  letI : LinearOrder W := o
  let D : RelStructure Lang W := forwardReduct C
  have hCopies : CopywiseCompletion B.ordered C.ordered D.ordered (fun x => x) :=
    forwardReduct_preserves_ordered_copies B C hB
  have hArrow : StructuralRamsey.Arrow A.ordered B.ordered D.ordered κ :=
    arrow_of_BCopywiseCompletion hRamsey hCopies
  exact ⟨W,hW,o,D,forwardReduct_edgesForward C,hArrow⟩

end AllThoseRamseyClasses.Applications.PaperGraphs
