import AllThoseRamseyClasses.Published.TrackEJointHybridExactInduce
import AllThoseRamseyClasses.Published.TrackEOldSplitHybridCanonical
import PartiteConstruction.Functional.WeakTransversalTests

/-!
# Track E2: canonical hybrid descriptions commute with GENUINE closed induction

The actual corrected 2019 functional class uses full embeddings and
function-closed induced substructures. An arbitrary weak vertex set S
is not function-closed: its native weak restriction clips fibres, while
the canonical original OLD mask keeps the original domain record.
The hybrid encoding must NEVER be recomputed from such a clipped
weak structure.

For a genuinely CLOSED subset S, however, there is an honest full
native induced structure and an actual full embedding back into A.
The merged hybrid full-embedding functor converts that inclusion
into a full hybrid relational embedding with the same vertex map.
Its relation-reflection property proves a literal equality:
  hybrid(A.induceClosed S) = hybrid(A).induce S.

The checked joint full-root tag/induction commutation then gives
exactly the same identity for the new joint-tagged hybrid language.
No closure hull is inserted; S was assumed closed from the start.
This is the correct source-side hereditary/closed-embedding
dictionary for an eventual hybrid multi-amalgamation class.

The theorem does NOT assert closure of arbitrary weak S,
normalization of arbitrary relational hybrid targets, class strong
amalgamation or a sparse Ramsey object. The distinction between
closed and arbitrary weak tests is essential to the 2019 correction.
-/

namespace StructuralRamsey.FunctionalPartite

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- The true native function-CLOSED induced partite System on the
exact existing carrier S. Both relation tuple and function-fibre
transversality descend without adding vertices. -/
def System.induceClosedExact (A : System L Parts V)
    (S : Set V) (hS : A.toStructure.IsClosed S) :
    System L Parts S where
  toStructure := A.toStructure.induce S hS
  part x := A.part x.1
  relTransversal := by
    intro R xs hR i j hPart
    apply Subtype.ext
    exact A.relTransversal R (Subtype.val ∘ xs) hR i j hPart
  funcTransversal := by
    intro F xs y z hy hz hPart
    apply Subtype.ext
    exact A.funcTransversal F (Subtype.val ∘ xs)
      y.1 z.1 hy hz hPart

/-- Full native induced inclusion at a function-CLOSED vertex set;
its underlying map is exactly Subtype.val and retains all parts. -/
def System.induceClosedExact_embedding
    (A : System L Parts V)
    (S : Set V) (hS : A.toStructure.IsClosed S) :
    Embedding (A.induceClosedExact S hS) A where
  toEmbedding := Structure.inclusion A.toStructure S hS
  map_part := fun _ => rfl

/-- On a TRUE function-CLOSED vertex set S, the canonical hybrid
source of the induced native partite System is LITERALLY the
ambient canonical hybrid relational structure induced on S.
Full reflection is essential: weak positivity alone cannot
recover complete original output masks on omitted outputs. -/
theorem System.induceClosedExact_splitMaskHybrid_eq
    (A : System L Parts V)
    (S : Set V) (hS : A.toStructure.IsClosed S) :
    (A.induceClosedExact S hS).splitMaskHybrid =
      A.splitMaskHybrid.induce S := by
  let e : Embedding (A.induceClosedExact S hS) A :=
    A.induceClosedExact_embedding S hS
  let eHybrid : RelStructure.Embedding
      (A.induceClosedExact S hS).splitMaskHybrid
      A.splitMaskHybrid :=
    AllThoseRamseyClasses.Published.systemEmbedding_splitMaskHybrid e
  apply RelStructure.rel_injective
  funext R xs
  exact propext (eHybrid.map_rel_iff R xs).symm

/-- The FULL joint hybrid-root tagged source has the same exact
closed-substructure dictionary, retaining all old domain/mask
predicates, split positive graph tuples, unary parts and fresh
full-hybrid-root tags on precisely S. This is a SOURCE theorem,
not a global completion of an arbitrary weak S. -/
theorem System.induceClosedExact_jointRoot_eq
    (A : System L Parts V)
    (S : Set V) (hS : A.toStructure.IsClosed S) :
    splitMaskJointRootExpansion
        (A.induceClosedExact S hS).splitMaskHybrid =
      (splitMaskJointRootExpansion A.splitMaskHybrid).induce S := by
  rw [A.induceClosedExact_splitMaskHybrid_eq S hS]
  exact splitMaskJointRootExpansion_induce_eq A.splitMaskHybrid S

end StructuralRamsey.FunctionalPartite
