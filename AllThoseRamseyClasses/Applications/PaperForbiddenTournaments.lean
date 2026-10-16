import AllThoseRamseyClasses.Applications.PaperForbiddenFamilies

/-!
# Arbitrary families of forbidden finite tournaments

This certifies the actual remark following cor:digraphs in the
2019 manuscript, for any indexed set of finite tournaments.
There is no uniform bound on their vertex counts or a finiteness
assumption on the forbidden family. Avoidance uses full (induced)
embeddings of directed graphs, including reflection of nonedges.

The result is a genuine finite ordered Ramsey class theorem, not
a conditional completion statement. Its proof reduces to the
family-of-irreducibles free-amalgamation criterion.
-/

namespace AllThoseRamseyClasses.Applications.PaperGraphs

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Applications.ForbiddenPatterns

universe w

/-- All finite digraphs with unrestricted edge relation and loops. -/
def finiteDigraphClass : StructureClass (L := Lang) :=
  fun {V} (_ : RelStructure Lang V) => Finite V

/-- A relational free amalgam of finite digraphs is finite since
the two source images cover its vertex carrier. -/
theorem finiteDigraphClass_freeAmalgamation :
    FreeAmalgamationClass finiteDigraphClass := by
  refine ⟨?_, ?_⟩
  · intro U V A B hB e
    letI : Finite V := hB
    exact Finite.of_injective e e.injective
  · intro H E F W D A B C sA sB iA iB hA hB hFree
    letI : Finite E := hA
    letI : Finite F := hB
    apply Finite.of_surjective
      (fun z : E ⊕ F => Sum.elim iA iB z)
    intro x
    rcases hFree.covers x with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact ⟨Sum.inl a, ha.symm⟩
    · exact ⟨Sum.inr b, hb.symm⟩

/-- An irreflexive orientation of every pair of distinct vertices. -/
def IsTournament {V : Type} (T : RelStructure Lang V) : Prop :=
  (∀ x : V, ¬ edge T x x) ∧
  (∀ x y : V, x ≠ y →
    (edge T x y ∧ ¬ edge T y x) ∨
    (edge T y x ∧ ¬ edge T x y))

theorem tournament_irreducible {V : Type}
    {T : RelStructure Lang V} (hT : IsTournament T) :
    T.Irreducible := by
  intro x y hxy
  rcases hT.2 x y hxy with h | h
  · exact ⟨.edge, ![x,y],0,1,h.1,rfl,rfl⟩
  · exact ⟨.edge, ![y,x],1,0,h.1,rfl,rfl⟩

/-- All finite digraphs avoiding a family of induced tournaments
of potentially different finite sizes. -/
def TournamentFreeClass {I : Type w} (n : I → ℕ)
    (T : (i : I) → RelStructure Lang (Fin (n i))) :
    StructureClass (L := Lang) :=
  ForbFamily finiteDigraphClass T

/-- The 2019 paper's forbidden-tournament application, with a
finite Ramsey witness for every finite ordered A,B and colour set. -/
theorem freelyOrderedTournamentFreeDigraphs_areRamsey
    {I : Type w} (n : I → ℕ)
    (T : (i : I) → RelStructure Lang (Fin (n i)))
    (hT : ∀ i : I, IsTournament (T i))
    {U V : Type} [Finite U] [Finite V]
    [LinearOrder U] [LinearOrder V]
    (A : RelStructure Lang U) (B : RelStructure Lang V)
    (hA : TournamentFreeClass n T A)
    (hB : TournamentFreeClass n T B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type) (_ : Finite W) (o : LinearOrder W)
      (C : RelStructure Lang W),
      TournamentFreeClass n T C ∧
      StructuralRamsey.Arrow A.ordered B.ordered
        (@RelStructure.ordered Lang W C o.toLT) κ :=
  orderedRamsey_avoiding_irreducible_family
    finiteDigraphClass_freeAmalgamation
    (fun i => tournament_irreducible (hT i))
    A B hA hB κ

end AllThoseRamseyClasses.Applications.PaperGraphs
