import AllThoseRamseyClasses.Applications.SteinerTripleHereditary
import PartiteConstruction.Iterated.FreeAmalgam
import PartiteConstruction.Ramsey.ClosureFreeAmalgamCompletion

/-!
# Free amalgams of strong Steiner systems retain their unique block roots

The underlying relational free amalgam does NOT yet have a total
vertex order across the sides, so it is not itself a member of the
freely ordered Steiner class. Nevertheless the *non-order closure*
invariant survives without modifying any block or covered-pair tuple.

The common root must be a genuine closed Steiner system and both
side maps must be FULL (strong subsystem) embeddings. The generic
2019 relational closure free-amalgam lemma applies exactly to
this data. It prohibits a second block output over a root's marked
pair even when the two inputs are glued across that root.

The later strong amalgamation proof still needs to extend the two
compatible linear orders, reflect every relation on the two input
sides, and establish all remaining normal-form laws of the target.
No strong-amalgamation or Ramsey assertion is made in this file.
-/

namespace AllThoseRamseyClasses.Applications.SteinerTriples

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The ACTUAL free relational amalgam of two well-formed ordered
partial Steiner triples over a well-formed common strong subsystem
is closed under the unique covered-pair block rule. The order
may remain incomplete between the two private sides. -/
theorem steiner_freeAmalgam_blockRules_closed
    {D E F : Type}
    (Root : RelStructure Lang D)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (hRoot : orderedSteinerClass Root)
    (hLeft : orderedSteinerClass Left)
    (hRight : orderedSteinerClass Right)
    (sL : Embedding Root Left) (sR : Embedding Root Right) :
    IsUClosed blockRules
      (FreeAmalgam.amalgam Root Left Right sL sR) := by
  classical
  exact (FreeAmalgam.isFreeAmalgam Root Left Right sL sR).isUClosed
    (orderedSteiner_isUClosed Root hRoot)
    (orderedSteiner_isUClosed Left hLeft)
    (orderedSteiner_isUClosed Right hRight)

/-- Every genuine increasing covered-pair root of the free
amalgam has exactly one ternary block tuple extension. In
particular, no two side blocks can assign different outputs
over the same full root after the prescribed identification. -/
theorem steiner_freeAmalgam_unique_block_extension
    {D E F : Type}
    (Root : RelStructure Lang D)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (hRoot : orderedSteinerClass Root)
    (hLeft : orderedSteinerClass Left)
    (hRight : orderedSteinerClass Right)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (e : Embedding pairRoot
      (FreeAmalgam.amalgam Root Left Right sL sR)) :
    ∃! t : Fin 3 →
        FreeAmalgam.Vertex Root Left Right sL sR,
      (FreeAmalgam.amalgam Root Left Right sL sR).rel .block t ∧
      ∀ i : Fin 2, t (i.castLE blockRule.rootLE) = e i := by
  have hClosed :=
    steiner_freeAmalgam_blockRules_closed
      Root Left Right hRoot hLeft hRight sL sR
  have hRule : blockRule ∈ blockRules := by
    simp only [blockRules, Set.mem_singleton_iff]
    rfl
  exact (hClosed blockRule hRule).2 e

end AllThoseRamseyClasses.Applications.SteinerTriples
