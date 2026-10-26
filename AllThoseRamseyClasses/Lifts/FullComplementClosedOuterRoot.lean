import AllThoseRamseyClasses.Lifts.GlobalFlipOuterRootPreservation

/-!
# Full functional embeddings transport closed source roots

For a genuinely set-valued partial-function Structure, a FULL
embedding maps complete function-value fibres ONTO the target
fibres on its image. Consequently both preimages and images of
function-closed vertex sets are closed. Mere weak positive
homomorphisms do not have this property in the reverse direction.

When an actual original source piece d is replaced through the
global canonical lift, its full closed complementary side is
embedded unchanged into the new forbidden source. An outer
minimal-separator root R disjoint from d's selected nonroot
component is function-closed in that complement, hence its
transported ordered-root range remains FUNCTION-CLOSED in
the replacement forbidden source.

This is stronger than equality of the outer root's target
coordinates (#631): the preserved root is still a genuine
closed native functional substructure. It does not prove
R remains an inclusion-MINIMAL separator, or that R plus
a transported component is an actual geometric piece.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w
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

/-- For any genuine source piece P and inner geometric piece d,
if the complete ordered outer root lies outside d's selected
nonroot component, then EVERY full native functional embedding
of d's old closed complement into an arbitrary replacement
source transports that entire old root to a FUNCTION-CLOSED set.

This statement needs no target EHN map and applies to the actual
complement embedding yielded by a B-to-A global source flip. -/
theorem geometricOuterRoot_closed_in_fullComplementReplacement
    {V : Type v} {W : Type w}
    (Source : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Source n)
    (d : GeometricFunctionalPieceData Source m)
    (New : Structure L W)
    (iComplement : Structure.Embedding
      (geometricGlobalComplementChart Source d).str New)
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Source
        (Set.range d.roots) d.left) :
    ∃ rootsInComplement : Fin n →
        (geometricGlobalComplementChart Source d).Carrier,
      (∀ i : Fin n, (rootsInComplement i).1 = P.roots i) ∧
      New.IsClosed (Set.range (iComplement ∘ rootsInComplement)) := by
  let Compl := geometricGlobalComplementChart Source d
  let rootsInComplement : Fin n → Compl.Carrier :=
    fun i => ⟨P.roots i, hOuterRootOutside i⟩
  have hRootsVal : ∀ i : Fin n, (rootsInComplement i).1 = P.roots i :=
    fun _ => rfl
  let oldCompl : Structure.Embedding Compl.str Source :=
    functionalComponentComplementEmbedding Source
      (Set.range d.roots) d.minimal.1 d.left
  let R : Set V := Set.range P.roots
  let RCompl : Set Compl.Carrier := oldCompl ⁻¹' R
  have hRComplClosed : Compl.str.IsClosed RCompl :=
    functionalEmbedding_preimage_closed
      Compl.str Source oldCompl R P.minimal.1
  have hImageClosed : New.IsClosed (iComplement '' RCompl) :=
    functionalEmbedding_image_closed
      Compl.str New iComplement RCompl hRComplClosed
  have hRange : Set.range (iComplement ∘ rootsInComplement) =
      iComplement '' RCompl := by
    apply Set.Subset.antisymm
    · rintro z ⟨i, rfl⟩
      refine ⟨rootsInComplement i, ?_, rfl⟩
      exact ⟨i, (hRootsVal i).symm⟩
    · rintro z ⟨b, hb, rfl⟩
      obtain ⟨i, hi⟩ := hb
      refine ⟨i, ?_⟩
      change iComplement (rootsInComplement i) = iComplement b
      congr 1
      apply Subtype.ext
      exact (hRootsVal i).trans hi
  refine ⟨rootsInComplement, hRootsVal, ?_⟩
  rw [hRange]
  exact hImageClosed

end AllThoseRamseyClasses.Lifts
