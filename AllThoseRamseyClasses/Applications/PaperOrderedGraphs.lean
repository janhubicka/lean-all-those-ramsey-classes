import PartiteConstruction.Ramsey.FreeAmalgamation
import PartiteConstruction.Ramsey.Ordered

/-!
# Two actual examples in the 2019 paper: freely ordered graphs and digraphs

These are the first two claims in Corollary cor:digraphs of the original
manuscript. The underlying language has ONE unrestricted binary relation.

* Directed graphs have no restrictions at all, including on diagonal
  tuples, exactly as in the paper; a free linear vertex order is added.
* Simple undirected graphs satisfy symmetry and irreflexivity. We prove
  genuine hereditary closure and full free amalgamation, then apply the
  checked Evans--Hubicka--Nesetril ordered free-amalgamation theorem.

The distinguished order is implemented as the upstream external
LinearOrder rather than a second stored binary relation. Ordered
relational embeddings in both conclusions are FULL embeddings and
therefore reflect both edges and nonedges; the ordered encoding is
equivalent to the manuscript's named reflexive order.
-/

namespace AllThoseRamseyClasses.Applications.PaperGraphs

open StructuralRamsey
open StructuralRamsey.RelStructure

inductive GraphSymbol
  | edge
  deriving DecidableEq

abbrev Lang : RelLanguage where
  Symbol := GraphSymbol
  arity := fun _ => 2

def edge {V : Type} (C : RelStructure Lang V) (x y : V) : Prop :=
  C.rel .edge ![x,y]

/-- Directed graphs in the paper carry no restrictions on their binary
relation: loops and both orientations are permitted. -/
theorem freelyOrderedDigraphs_areRamsey
    {U V : Type} [Finite U] [Finite V]
    [LinearOrder U] [LinearOrder V]
    (A : RelStructure Lang U) (B : RelStructure Lang V)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type) (_ : Finite W) (o : LinearOrder W)
      (C : RelStructure Lang W),
      StructuralRamsey.Arrow A.ordered B.ordered
        (@RelStructure.ordered Lang W C o.toLT) κ :=
  StructuralRamsey.Partite.orderedRamsey A B κ

/-- Finite simple undirected graphs, with no chosen vertex order yet. -/
def simpleGraphClass : StructureClass (L := Lang) :=
  fun {V} (C : RelStructure Lang V) =>
    Finite V ∧
    (∀ x : V, ¬ edge C x x) ∧
    (∀ x y : V, edge C x y → edge C y x)

/-- Full embeddings preserve and reflect the single edge relation. -/
theorem edge_embedding_iff
    {U V : Type} {A : RelStructure Lang U} {B : RelStructure Lang V}
    (e : Embedding A B) (x y : U) :
    edge B (e x) (e y) ↔ edge A x y := by
  have ht : e ∘ ![x,y] = ![e x,e y] := by
    funext i
    fin_cases i <;> rfl
  change B.rel .edge ![e x,e y] ↔ A.rel .edge ![x,y]
  rw [← ht]
  exact e.map_rel_iff .edge ![x,y]

/-- Ordinary exact induced hereditary closure for simple graphs. -/
theorem simpleGraphClass_hereditary
    {U V : Type} {A : RelStructure Lang U} {B : RelStructure Lang V}
    (hB : simpleGraphClass B) (e : Embedding A B) :
    simpleGraphClass A := by
  refine ⟨Finite.of_injective e e.injective, ?_, ?_⟩
  · intro x hx
    exact hB.2.1 (e x) ((edge_embedding_iff e x x).mpr hx)
  · intro x y hxy
    apply (edge_embedding_iff e y x).mp
    exact hB.2.2 (e x) (e y)
      ((edge_embedding_iff e x y).mpr hxy)

/-- Convert a positive edge from a free amalgam into its
full source-side ordered pair, without assuming any cross edges. -/
private theorem positive_edge_side
    {H E F P : Type}
    {D : RelStructure Lang H} {A : RelStructure Lang E}
    {B : RelStructure Lang F} {C : RelStructure Lang P}
    {sA : Embedding D A} {sB : Embedding D B}
    {iA : Embedding A C} {iB : Embedding B C}
    (hFree : IsFreeAmalgam sA sB iA iB) {x y : P}
    (h : edge C x y) :
    (∃ a b : E, edge A a b ∧ x = iA a ∧ y = iA b) ∨
    (∃ a b : F, edge B a b ∧ x = iB a ∧ y = iB b) := by
  rcases (hFree.rel_iff .edge ![x,y]).mp h with
      ⟨t,hRel,hEq⟩ | ⟨t,hRel,hEq⟩
  · left
    refine ⟨t 0,t 1,?_,?_,?_⟩
    · change A.rel .edge ![t 0,t 1]
      have ht : (![t 0,t 1] : Fin 2 → E) = t := by
        funext i
        fin_cases i <;> rfl
      rw [ht]
      exact hRel
    · simpa only [Function.comp_apply] using congrFun hEq 0
    · simpa only [Function.comp_apply] using congrFun hEq 1
  · right
    refine ⟨t 0,t 1,?_,?_,?_⟩
    · change B.rel .edge ![t 0,t 1]
      have ht : (![t 0,t 1] : Fin 2 → F) = t := by
        funext i
        fin_cases i <;> rfl
      rw [ht]
      exact hRel
    · simpa only [Function.comp_apply] using congrFun hEq 0
    · simpa only [Function.comp_apply] using congrFun hEq 1

/-- The symmetric irreflexive graphs form a genuine finite relational
free-amalgamation class, with no extra identified vertices. -/
theorem simpleGraphClass_freeAmalgamation :
    FreeAmalgamationClass simpleGraphClass := by
  refine ⟨?_, ?_⟩
  · intro U V A B hB e
    exact simpleGraphClass_hereditary hB e
  · intro H E F P D A B C sA sB iA iB hA hB hFree
    letI : Finite E := hA.1
    letI : Finite F := hB.1
    have hFiniteP : Finite P := by
      apply Finite.of_surjective
        (fun z : E ⊕ F => Sum.elim iA iB z)
      intro p
      rcases hFree.covers p with ⟨a,ha⟩ | ⟨b,hb⟩
      · exact ⟨Sum.inl a,ha.symm⟩
      · exact ⟨Sum.inr b,hb.symm⟩
    refine ⟨hFiniteP, ?_, ?_⟩
    · intro x hxx
      rcases positive_edge_side hFree hxx with
          ⟨a,b,hab,hx,hy⟩ | ⟨a,b,hab,hx,hy⟩
      · have hEq : a = b := iA.injective (hx.symm.trans hy)
        subst b
        exact hA.2.1 a hab
      · have hEq : a = b := iB.injective (hx.symm.trans hy)
        subst b
        exact hB.2.1 a hab
    · intro x y hxy
      rcases positive_edge_side hFree hxy with
          ⟨a,b,hab,hx,hy⟩ | ⟨a,b,hab,hx,hy⟩
      · have hba : edge A b a := hA.2.2 a b hab
        apply (hFree.rel_iff .edge ![y,x]).mpr
        left
        refine ⟨![b,a],hba,?_⟩
        funext i
        fin_cases i
        · exact hy
        · exact hx
      · have hba : edge B b a := hB.2.2 a b hab
        apply (hFree.rel_iff .edge ![y,x]).mpr
        right
        refine ⟨![b,a],hba,?_⟩
        funext i
        fin_cases i
        · exact hy
        · exact hx

/-- The actual undirected half of cor:digraphs: no conditional
amalgamation, completion, or ambient Ramsey hypothesis remains. -/
theorem freelyOrderedSimpleGraphs_areRamsey
    {U V : Type} [Finite U] [Finite V]
    [LinearOrder U] [LinearOrder V]
    (A : RelStructure Lang U) (B : RelStructure Lang V)
    (hA : simpleGraphClass A) (hB : simpleGraphClass B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type) (_ : Finite W) (o : LinearOrder W)
      (C : RelStructure Lang W),
      simpleGraphClass C ∧
      StructuralRamsey.Arrow A.ordered B.ordered
        (@RelStructure.ordered Lang W C o.toLT) κ :=
  FreeAmalgamationClass.orderedRamsey
    simpleGraphClass_freeAmalgamation A B hA hB κ

end AllThoseRamseyClasses.Applications.PaperGraphs
