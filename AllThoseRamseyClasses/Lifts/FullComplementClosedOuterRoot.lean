import AllThoseRamseyClasses.Lifts.GlobalFlipOuterRootPreservation

/-!
# Full functional embeddings transport closed source roots

For a genuinely set-valued partial-function Structure, a FULL
embedding maps complete function-value fibres ONTO the target
fibres on its image. Consequently both preimages and images of
function-closed vertex sets are closed. Mere weak positive
homomorphisms do not have this property in the reverse direction.

When an actual source piece is replaced through the full canonical
lift, its old closed complement is embedded unchanged. If an old
minimal-separator root is contained in that complement, the
transported ordered root range remains FUNCTION-CLOSED in the
replacement forbidden source. The proof is phrased generically
using two full embeddings of the SAME complement, which avoids
unnecessary dependence on the specific free-amalgam carrier.

This is stronger than equality of the outer root's target
coordinates (#631): the preserved root is still a genuine
closed native functional substructure. It does not prove
R remains an inclusion-MINIMAL separator, or that R plus
a transported component is an actual geometric piece.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w z
variable {L : Language.{u}}

/-- Inverse images of function-closed sets along FULL functional
embeddings remain function-closed in the complete native sense,
including arbitrary output fibres and nullary operations. -/
theorem functionalEmbedding_preimage_closed
    {V : Type v} {W : Type w}
    (A : Structure L V) (B : Structure L W)
    (e : Structure.Embedding A B)
    (T : Set W) (hT : B.IsClosed T) :
    A.IsClosed (e ⁻¹' T) := by
  intro F xs hxs y hy
  have hImage : e y ∈ B.func F (e ∘ xs) := by
    rw [← e.map_func F xs]
    exact ⟨y, hy, rfl⟩
  exact hT F (e ∘ xs) hxs hImage

/-- Images of function-closed vertex sets under FULL functional
embeddings are function-closed in the target; this uses equality
of entire function fibres, not only positive preservation. -/
theorem functionalEmbedding_image_closed
    {V : Type v} {W : Type w}
    (A : Structure L V) (B : Structure L W)
    (e : Structure.Embedding A B)
    (S : Set V) (hS : A.IsClosed S) :
    B.IsClosed (e '' S) := by
  classical
  intro F xs hxs y hy
  choose pre hpre using hxs
  have hArgs : e ∘ pre = xs := by
    funext i
    exact (hpre i).2
  have hImage : y ∈ imageSet e (A.func F pre) := by
    rw [e.map_func F pre, hArgs]
    exact hy
  rcases hImage with ⟨z, hz, rfl⟩
  exact ⟨z, hS F pre (fun i => (hpre i).1) hz, rfl⟩

/-- Transport a genuine old minimal-separator root across two
FULL embeddings of a common native complement.

The tuple `roots` lists the COMPLETE old separator root through
the original complement embedding. This ensures the preimage
of the closed old root is precisely the range of that tuple;
its image under the NEW full complement embedding is therefore
still closed in the replacement source. No claim of geometric
separator minimality in the replacement is made. -/
theorem geometricOuterRoot_closed_under_fullComplementTransport
    {V : Type v} {C : Type w} {W : Type z}
    (Source : Structure L V)
    {n : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (Complement : Structure L C)
    (oldComplement : Structure.Embedding Complement Source)
    (New : Structure L W)
    (newComplement : Structure.Embedding Complement New)
    (roots : Fin n → C)
    (hOldRoots : ∀ i : Fin n,
      oldComplement (roots i) = P.roots i) :
    New.IsClosed (Set.range (newComplement ∘ roots)) := by
  let R : Set V := Set.range P.roots
  let RCompl : Set C := oldComplement ⁻¹' R
  have hOldClosed : Complement.IsClosed RCompl :=
    functionalEmbedding_preimage_closed
      Complement Source oldComplement R P.minimal.1
  have hNewClosed : New.IsClosed (newComplement '' RCompl) :=
    functionalEmbedding_image_closed
      Complement New newComplement RCompl hOldClosed
  have hRange : Set.range (newComplement ∘ roots) =
      newComplement '' RCompl := by
    apply Set.Subset.antisymm
    · rintro z ⟨i, rfl⟩
      refine ⟨roots i, ?_, rfl⟩
      exact ⟨i, (hOldRoots i).symm⟩
    · rintro z ⟨c, ⟨i, hi⟩, rfl⟩
      refine ⟨i, ?_⟩
      have hEq : roots i = c :=
        oldComplement.injective ((hOldRoots i).trans hi)
      exact congrArg newComplement hEq
  rw [hRange]
  exact hNewClosed

end AllThoseRamseyClasses.Lifts
