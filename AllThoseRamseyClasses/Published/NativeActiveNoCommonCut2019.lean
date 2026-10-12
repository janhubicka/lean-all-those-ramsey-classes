import AllThoseRamseyClasses.Published.NativeFiniteActiveHistory2019
import AllThoseRamseyClasses.Published.NativeTransverseActiveCut2019

/-!
# Corrected 2019 native Picture: no-common-coordinate ACTIVE test gives proper cut

The exact private-active line set of a finite test is now a CONSTRUCTED
finite set (PR #147), not an arbitrary selected family endowed with an
independent activity premise (PR #143). Thus every index in this actual
active set comes with a witness in the ORIGINAL tested weak source.

For an actual native source map, if that finite active set is nonempty
and lacks one coordinate variable on every active line, the true copy/rest
source free decomposition has two proper sides of at most rank vertices
when the tested source has at most rank+1 vertices.

No global injectivity of the protected map, U-closedness of the weak
source, or U-semiclosedness of the temporary native target is used.
A chosen MINIMAL transverse subfamily still need not contain all active
indices, and an ordinary old-Picture REST map may not exist on the whole
active remainder. The vertex-level common A-root is not constructed.
Nothing here proves the unrestricted repaired Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment
open StructuralRamsey.HalesJewett

universe u v
variable {L : RelLanguage.{u}}

/-- The finite set of ALL source-private-active native line indices,
with no independent activity assumption, forces a strict, small free
source cut if it is nonempty and has no common HJ parameter coordinate.
It uses the actual original tested vertex carrier, not its hull. -/
theorem native2019_exact_active_no_common_small_free_cut
    {U V W I Alphabet : Type v} {N : ℕ}
    [Fintype U]
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphism (attach Old Support Core maps) p)
    (lines : I → Line Alphabet N)
    (rank : ℕ) (hCard : Fintype.card U ≤ rank + 1)
    (hActiveNonempty :
      (native2019_exact_active_index_finset Support p).Nonempty)
    (hNoCommon : ¬ ∃ k : Fin N,
      ∀ i ∈ native2019_exact_active_index_finset Support p,
        (lines i).symbol k = .parameter) :
    ∃ d : ProperFreeDecomposition Source,
      Nat.card d.Left ≤ rank ∧ Nat.card d.Right ≤ rank := by
  let T : Finset I := native2019_exact_active_index_finset Support p
  have hEachActive : ∀ i ∈ T, ∃ x : U,
      OutsideAt (W := W) (I := I) Support i (p x) := by
    intro i hi
    exact (native2019_mem_exact_active_index_iff Support p i).mp hi
  exact native2019_transverse_active_family_small_free_cut
    Source Old Support Core maps p hp
    lines T hActiveNonempty hNoCommon
    hEachActive rank hCard

end AllThoseRamseyClasses.Published
