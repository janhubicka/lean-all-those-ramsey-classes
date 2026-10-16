import AllThoseRamseyClasses.Applications.PaperForbiddenTournaments

/-!
# Henson-style oriented graphs forbidding positive tournament copies

The paper's tournament-free digraphs conventionally forbid copies
as POSITIVE directed subgraphs. The general ForbFamily theorem
forbids FULL/INDUCED copies instead. For oriented graphs (no
loops, no opposite arcs), an injective positive embedding of a
tournament is automatically a full embedding. We certify this
bridge and the actual freely ordered Ramsey theorem.

The ambient class is irreflexive oriented graphs, not all digraphs
with loops and two-way edges. An arbitrary indexed family of
finite tournaments is permitted, with unbounded sizes.
-/

namespace AllThoseRamseyClasses.Applications.PaperGraphs

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Applications.ForbiddenPatterns

universe w

/-- Finite directed graphs with no loops or opposite arcs. -/
def orientedDigraphClass : StructureClass (L := Lang) :=
  fun {V} (C : RelStructure Lang V) =>
    Finite V ∧
    (∀ x : V, ¬ edge C x x) ∧
    (∀ x y : V, edge C x y → ¬ edge C y x)

/-- The class of finite oriented graphs is closed under full
substructures and has full free amalgamation. -/
theorem orientedDigraphClass_freeAmalgamation :
    FreeAmalgamationClass orientedDigraphClass := by
  refine ⟨?_, ?_⟩
  · intro U V A B hB e
    letI : Finite V := hB.1
    refine ⟨Finite.of_injective e e.injective, ?_, ?_⟩
    · intro x hx
      exact hB.2.1 (e x) ((edge_embedding_iff e x x).mpr hx)
    · intro x y hxy hyx
      exact (hB.2.2 (e x) (e y)
        ((edge_embedding_iff e x y).mpr hxy))
        ((edge_embedding_iff e y x).mpr hyx)
  · intro H E F P D A B C sA sB iA iB hA hB hFree
    letI : Finite E := hA.1
    letI : Finite F := hB.1
    have hFiniteP : Finite P := by
      apply Finite.of_surjective
        (fun z : E ⊕ F => Sum.elim iA iB z)
      intro p
      rcases hFree.covers p with ⟨a, ha⟩ | ⟨b, hb⟩
      · exact ⟨Sum.inl a, ha.symm⟩
      · exact ⟨Sum.inr b, hb.symm⟩
    refine ⟨hFiniteP, ?_, ?_⟩
    · intro x hxx
      rcases positive_edge_side hFree hxx with
        ⟨a,b,hab,hx,hy⟩ | ⟨a,b,hab,hx,hy⟩
      · have heq : a = b := iA.injective (hx.symm.trans hy)
        subst b
        exact hA.2.1 a hab
      · have heq : a = b := iB.injective (hx.symm.trans hy)
        subst b
        exact hB.2.1 a hab
    · intro x y hxy hyx
      rcases positive_edge_side hFree hxy with
        ⟨a,b,hab,hx,hy⟩ | ⟨a,b,hab,hx,hy⟩
      · have hba : edge A b a :=
          (edge_embedding_iff iA b a).mp (by
            rw [hy, hx] at hyx
            exact hyx)
        exact (hA.2.2 a b hab) hba
      · have hba : edge B b a :=
          (edge_embedding_iff iB b a).mp (by
            rw [hy, hx] at hyx
            exact hyx)
        exact (hB.2.2 a b hab) hba

/-- Injective positive edge-preserving map; it is NOT required
to reflect missing edges or nonrelations. -/
def PositiveCopy {U V : Type}
    (A : RelStructure Lang U) (B : RelStructure Lang V) : Prop :=
  ∃ f : U → V, Function.Injective f ∧
    ∀ x y : U, edge A x y → edge B (f x) (f y)

/-- Every full induced embedding is a positive copy. -/
theorem positiveCopy_of_embedding {U V : Type}
    {A : RelStructure Lang U} {B : RelStructure Lang V}
    (e : Embedding A B) : PositiveCopy A B :=
  ⟨e, e.injective, fun x y hxy =>
    (edge_embedding_iff e x y).mpr hxy⟩

/-- In an oriented target, every injective positive tournament
copy is necessarily induced: all missing opposite arcs are
reflected because the target forbids digons, and loops are absent. -/
theorem tournament_embedding_of_positiveCopy
    {U V : Type} {T : RelStructure Lang U}
    {C : RelStructure Lang V}
    (hT : IsTournament T) (hOriented : orientedDigraphClass C)
    (hcopy : PositiveCopy T C) :
    Nonempty (Embedding T C) := by
  obtain ⟨f, hf, hpos⟩ := hcopy
  refine ⟨{toFun := f, injective := hf, map_rel_iff := ?_}⟩
  intro R t
  cases R with
  | edge =>
      change edge C (f (t 0)) (f (t 1)) ↔
        edge T (t 0) (t 1)
      constructor
      · intro hEdge
        by_cases hEq : t 0 = t 1
        · have hloop : edge C (f (t 1)) (f (t 1)) := by
            simpa only [hEq] using hEdge
          exact False.elim (hOriented.2.1 (f (t 1)) hloop)
        · rcases hT.2 (t 0) (t 1) hEq with hfwd | hback
          · exact hfwd.1
          · have hrev : edge C (f (t 1)) (f (t 0)) :=
              hpos (t 1) (t 0) hback.1
            exact False.elim ((hOriented.2.2 (f (t 1)) (f (t 0)) hrev) hEdge)
      · exact hpos (t 0) (t 1)

/-- Finite oriented digraphs omitting any positive tournament
copy, of any member of a set-sized family. -/
def PositiveTournamentFreeClass {I : Type w} (n : I → ℕ)
    (T : (i : I) → RelStructure Lang (Fin (n i))) :
    StructureClass (L := Lang) :=
  fun C => orientedDigraphClass C ∧
    ∀ i : I, ¬ PositiveCopy (T i) C

/-- On oriented targets, induced avoidance and positive tournament
avoidance are exactly equivalent, not merely one-way implications. -/
theorem positiveTournamentFree_iff_ForbFamily
    {I : Type w} (n : I → ℕ)
    (T : (i : I) → RelStructure Lang (Fin (n i)))
    (hT : ∀ i : I, IsTournament (T i))
    {V : Type} (C : RelStructure Lang V) :
    PositiveTournamentFreeClass n T C ↔
      ForbFamily orientedDigraphClass T C := by
  constructor
  · rintro ⟨hC, hno⟩
    refine ⟨hC, ?_⟩
    intro i ⟨e⟩
    exact hno i (positiveCopy_of_embedding e)
  · rintro ⟨hC, hno⟩
    refine ⟨hC, ?_⟩
    intro i hc
    exact hno i (tournament_embedding_of_positiveCopy (hT i) hC hc)

/-- The literal Henson-style forbidden-tournament Ramsey conclusion:
full vertex orders are free, but the forbidden positive directed
subgraphs can be an arbitrary indexed family of tournaments. -/
theorem freelyOrderedPositiveTournamentFreeDigraphs_areRamsey
    {I : Type w} (n : I → ℕ)
    (T : (i : I) → RelStructure Lang (Fin (n i)))
    (hT : ∀ i : I, IsTournament (T i))
    {U V : Type} [Finite U] [Finite V]
    [LinearOrder U] [LinearOrder V]
    (A : RelStructure Lang U) (B : RelStructure Lang V)
    (hA : PositiveTournamentFreeClass n T A)
    (hB : PositiveTournamentFreeClass n T B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type) (_ : Finite W) (o : LinearOrder W)
      (C : RelStructure Lang W),
      PositiveTournamentFreeClass n T C ∧
      StructuralRamsey.Arrow A.ordered B.ordered
        (@RelStructure.ordered Lang W C o.toLT) κ := by
  have hA' : ForbFamily orientedDigraphClass T A :=
    (positiveTournamentFree_iff_ForbFamily n T hT A).mp hA
  have hB' : ForbFamily orientedDigraphClass T B :=
    (positiveTournamentFree_iff_ForbFamily n T hT B).mp hB
  obtain ⟨W, hW, o, C, hC, hArrow⟩ :=
    orderedRamsey_avoiding_irreducible_family
      orientedDigraphClass_freeAmalgamation
      (fun i => tournament_irreducible (hT i))
      A B hA' hB' κ
  exact ⟨W, hW, o, C,
    (positiveTournamentFree_iff_ForbFamily n T hT C).mpr hC,
    hArrow⟩

end AllThoseRamseyClasses.Applications.PaperGraphs
