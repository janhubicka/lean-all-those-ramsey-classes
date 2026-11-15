import PartiteConstruction.Functional.WeakInvariant
import Mathlib.Data.Fintype.Card

/-!
# Finite irreducible test cardinality obstructs a weak EHN source map

By the definition of EHN homomorphism-embedding, EVERY
genuinely irreducible FULL source test T embedded into a
possibly reducible source Q must admit a FULL embedding into
the target X, agreeing with the weak source map on that test.

Consequently if T has MORE vertices than a finite X, NO
EHN homomorphism-embedding Q -> X exists. This is a literal
finite SOURCE test obstruction; even if Q is reducible and
the weak map could identify other source vertices, it cannot
identify the vertices of a single irreducible FULL test.

This is designed to supply the structural no-EHN premise of
the Track C selected-Q A-neutrality obstruction, rather than
assuming no weak Q-to-X factor exists by inspection.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An EHN homomorphism-embedding of a genuine source Q into X
induces an actual FULL embedding of every irreducible
source substructure TEST into X. With TEST and X finite,
its true SOURCE-vertex count cannot exceed |X|. -/
theorem weakEHN_irreducibleFullTest_card_le_target
    {Q T UX : Type}
    [Finite T] [Finite UX]
    (Piece : Structure L Q)
    (Test : Structure L T)
    (hIrreducible : Test.Irreducible)
    (eTest : Structure.Embedding Test Piece)
    (X : Structure L UX)
    (p : Q → UX)
    (hp : Piece.IsEHNHomomorphismEmbedding X p) :
    Nat.card T ≤ Nat.card UX := by
  obtain ⟨g, _hg⟩ := hp.2 Test hIrreducible eTest
  exact Nat.card_le_card_of_injective g g.injective

/-- If an irreducible FULL source test has strictly MORE
source vertices than the finite proposed common root X,
NO EHN homomorphism-embedding of the entire source Piece
to X is possible, regardless of any collisions on other
reducible parts of Piece. -/
theorem weakEHN_no_map_into_smaller_commonRoot_of_fullTest
    {Q T UX : Type}
    [Finite T] [Finite UX]
    (Piece : Structure L Q)
    (Test : Structure L T)
    (hIrreducible : Test.Irreducible)
    (eTest : Structure.Embedding Test Piece)
    (X : Structure L UX)
    (hTooLarge : Nat.card UX < Nat.card T) :
    ∀ p : Q → UX,
      ¬ Piece.IsEHNHomomorphismEmbedding X p := by
  intro p hp
  exact (Nat.not_lt_of_ge
    (weakEHN_irreducibleFullTest_card_le_target
      Piece Test hIrreducible eTest X p hp)) hTooLarge

end AllThoseRamseyClasses.Lifts
