import AllThoseRamseyClasses.Applications.PaperPositiveForbiddenFamilies
import AllThoseRamseyClasses.Applications.PaperForbiddenTournaments

/-!
# Positive forbidden-tournament Ramsey for all finite digraphs

The manuscript describes finite digraphs omitting a given family of
tournaments. A positive copy of a tournament is an injective map
preserving ALL directed edges of that tournament, without requiring
missing reverse arcs or loops to be reflected.

This is stronger avoidance than forbidding induced copies. Unlike
the oriented-graph specialization, the ambient digraphs here may
have loops and opposite arcs. The finite ordered Ramsey theorem
follows from the general verified positive-irreduci­ble-family
construction, via all full extensions of each tournament.

No uniform finite bound on tournament sizes and no finiteness
assumption on the family of forbidden tournaments is imposed.
-/

namespace AllThoseRamseyClasses.Applications.PaperGraphs

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Applications.ForbiddenPatterns

universe w

/-- The class of finite unrestricted digraphs omitting every
forbidden tournament as a positive (not necessarily induced)
directed subgraph. -/
def PositiveTournamentFreeDigraphClass
    {I : Type w} (n : I → ℕ)
    (T : (i : I) → RelStructure Lang (Fin (n i))) :
    StructureClass (L := Lang) :=
  ForbPositiveFamily finiteDigraphClass T

/-- The paper's tournament-omission remark under the ordinary
positive-subgraph interpretation, with no restriction forbidding
loops or opposite arcs in the ambient digraph class. Every
Ramsey witness is finite and every copy to be coloured is a
full order-preserving embedding. -/
theorem freelyOrderedPositiveTournamentFreeAllDigraphs_areRamsey
    {I : Type w} (n : I → ℕ)
    (T : (i : I) → RelStructure Lang (Fin (n i)))
    (hT : ∀ i : I, IsTournament (T i))
    {U V : Type} [Finite U] [Finite V]
    [LinearOrder U] [LinearOrder V]
    (A : RelStructure Lang U) (B : RelStructure Lang V)
    (hA : PositiveTournamentFreeDigraphClass n T A)
    (hB : PositiveTournamentFreeDigraphClass n T B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type) (_ : Finite W) (o : LinearOrder W)
      (C : RelStructure Lang W),
      PositiveTournamentFreeDigraphClass n T C ∧
      StructuralRamsey.Arrow A.ordered B.ordered
        (@RelStructure.ordered Lang W C o.toLT) κ :=
  orderedRamsey_avoiding_positive_irreducible_family
    finiteDigraphClass_freeAmalgamation
    (fun i => tournament_irreducible (hT i))
    A B hA hB κ

end AllThoseRamseyClasses.Applications.PaperGraphs
