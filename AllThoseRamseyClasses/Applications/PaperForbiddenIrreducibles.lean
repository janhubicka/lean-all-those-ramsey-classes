import AllThoseRamseyClasses.Applications.PaperOrderedGraphs
import PartiteConstruction.Ramsey.FreeAmalgamation

/-!
# Forbidden irreducible patterns: the K_n-free graph example in 2019

The paper remarks after cor:digraphs that freely ordered finite K_n-free
graphs (and forbidden-tournament digraphs) are Ramsey.  The reusable reason
is that a FULL embedding of an irreducible forbidden pattern into a free
amalgam must lie wholly inside one amalgamation side.

The criterion below is language-polymorphic and works for any hereditary
relational free-amalgamation class.  No extra Ramsey construction is
needed.  Our concrete specialization forbids an induced complete graph
on n vertices in finite undirected simple graphs.  For complete graphs,
an induced copy is exactly an ordinary n-clique, since every unordered
pair is already an edge.

This is the *finite*, freely ordered class Ramsey property, represented
by an external strict linear vertex order and full embeddings.
-/

namespace AllThoseRamseyClasses.Applications.ForbiddenPatterns

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {P : Type v}

/-- Full-embedding avoidance, with membership in the original class. -/
def ForbOne (K : StructureClass.{u,v} (L := L))
    (Forbidden : RelStructure L P) : StructureClass.{u,v} (L := L) :=
  fun C => K C ∧ ¬ Nonempty (Embedding Forbidden C)

/-- Avoidance of an irreducible pattern is preserved by full
substructures and arbitrary full relational free amalgamation.
The target class K may have other, unrelated local axioms. -/
theorem freeAmalgamation_of_irreducible_forbidden
    {K : StructureClass.{u,v} (L := L)}
    {Forbidden : RelStructure L P}
    (hK : FreeAmalgamationClass K)
    (hForbidden : Forbidden.Irreducible) :
    FreeAmalgamationClass (ForbOne K Forbidden) := by
  refine ⟨?_, ?_⟩
  · intro U V A B hB e
    refine ⟨hK.hereditary hB.1 e, ?_⟩
    intro ⟨f⟩
    exact hB.2 ⟨e.comp f⟩
  · intro H E F W D A B C sA sB iA iB hA hB hFree
    refine ⟨hK.free hA.1 hB.1 hFree, ?_⟩
    intro ⟨e⟩
    have hRangeIrred : (C.induce (Set.range e)).Irreducible :=
      hForbidden.range_embedding e
    rcases hFree.irreducible_side (Set.range e) hRangeIrred with
        hLeft | hRight
    · have hRange : ∀ x : P, ∃ a : E, e x = iA a := by
        intro x
        obtain ⟨a, ha⟩ := hLeft ⟨e x, ⟨x, rfl⟩⟩
        exact ⟨a, ha⟩
      exact hA.2 ⟨e.factorThroughRange iA hRange⟩
    · have hRange : ∀ x : P, ∃ b : F, e x = iB b := by
        intro x
        obtain ⟨b, hb⟩ := hRight ⟨e x, ⟨x, rfl⟩⟩
        exact ⟨b, hb⟩
      exact hB.2 ⟨e.factorThroughRange iB hRange⟩

/-- Ordered Ramsey for members avoiding one irreducible pattern,
with no conditional completion or amalgamation premise beyond the
actually proved free-amalgamation class field. -/
theorem orderedRamsey_avoiding_irreducible
    {K : StructureClass.{u,v} (L := L)}
    {Forbidden : RelStructure L P}
    (hK : FreeAmalgamationClass K)
    (hForbidden : Forbidden.Irreducible)
    {U V : Type v} [Finite U] [Finite V]
    [LinearOrder U] [LinearOrder V]
    (A : RelStructure L U) (B : RelStructure L V)
    (hA : ForbOne K Forbidden A) (hB : ForbOne K Forbidden B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : RelStructure L W),
      ForbOne K Forbidden C ∧
      StructuralRamsey.Arrow A.ordered B.ordered
        (@RelStructure.ordered L W C o.toLT) κ :=
  FreeAmalgamationClass.orderedRamsey
    (freeAmalgamation_of_irreducible_forbidden hK hForbidden)
    A B hA hB κ

end AllThoseRamseyClasses.Applications.ForbiddenPatterns

namespace AllThoseRamseyClasses.Applications.PaperGraphs

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Applications.ForbiddenPatterns

/-- The undirected complete graph on Fin n, without loops.
n=0,1 are included for a uniform formal signature. -/
def clique (n : ℕ) : RelStructure Lang (Fin n) where
  rel := fun
    | .edge, t => t 0 ≠ t 1

theorem clique_irreducible (n : ℕ) : (clique n).Irreducible := by
  intro x y hxy
  exact ⟨.edge, ![x,y],0,1,hxy,rfl,rfl⟩

theorem clique_simple (n : ℕ) : simpleGraphClass (clique n) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro x hx
    exact hx rfl
  · intro x y hxy
    exact hxy.symm

/-- A finite simple graph has no induced K_n; equivalently, it has
no ordinary n-clique because K_n lists every pair of distinct edges. -/
def KnFreeClass (n : ℕ) : StructureClass (L := Lang) :=
  ForbOne simpleGraphClass (clique n)

/-- The K_n-free undirected graph class has the actual hereditary and
full free-amalgamation axioms, for every finite n. -/
theorem KnFreeClass_freeAmalgamation (n : ℕ) :
    FreeAmalgamationClass (KnFreeClass n) :=
  freeAmalgamation_of_irreducible_forbidden
    simpleGraphClass_freeAmalgamation (clique_irreducible n)

/-- The paper's K_n-free graph remark, for any finite forbidden n.
All colourings concern FULL order-preserving embeddings of graphs. -/
theorem freelyOrderedKnFreeGraphs_areRamsey
    (n : ℕ)
    {U V : Type} [Finite U] [Finite V]
    [LinearOrder U] [LinearOrder V]
    (A : RelStructure Lang U) (B : RelStructure Lang V)
    (hA : KnFreeClass n A) (hB : KnFreeClass n B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type) (_ : Finite W) (o : LinearOrder W)
      (C : RelStructure Lang W),
      KnFreeClass n C ∧
      StructuralRamsey.Arrow A.ordered B.ordered
        (@RelStructure.ordered Lang W C o.toLT) κ :=
  FreeAmalgamationClass.orderedRamsey
    (KnFreeClass_freeAmalgamation n) A B hA hB κ

end AllThoseRamseyClasses.Applications.PaperGraphs
