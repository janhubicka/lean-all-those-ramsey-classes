import AllThoseRamseyClasses.Lifts.GeometricGlobalPieceSymbol
import AllThoseRamseyClasses.Lifts.WeakSourceFreeAmalgamPartition

/-!
# Recover common-root coordinates from the actual weak source map

The 2019 flip mechanism uses one ordered tuple xsX of vertices of
the common full functional root X. It should not assume those
coordinates as an independent oracle when the geometric source
cut is already known to map into X.

For every root vertex of a genuine selected piece, the weak source
map lands in the range of the full embedding X -> Left -> Target.
A full factorization of the piece map into Left then supplies a
unique Left-vertex above that target image. Injectivity of the
FULL inclusion Left -> Target recovers a matching X-coordinate.

This constructs the shared tuple even when DISTINCT SOURCE root
vertices have the SAME image (xsX itself may be noninjective).
It does not infer root-image injectivity, a folded lift, or any
unconditional geometric flip.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A full left-side map of an ACTUAL geometric forbidden piece,
together with exact membership of all source roots in the
common-root PREIMAGE, yields the common ordered tuple needed
for the true global and auxiliary folded lift flip mechanisms.

No coordinate injectivity is assumed or concluded. -/
theorem geometricPiece_commonRootCoordinates
    {V UX UA UT : Type}
    (A : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData A n)
    (Target : Structure L UT) (f : V → UT)
    (X : Structure L UX) (Left : Structure L UA)
    (iLeft : Structure.Embedding X Left)
    (jLeft : Structure.Embedding Left Target)
    (pLeft : (geometricGlobalFunctionalChart A d).ext.Carrier → UA)
    (hPieceMap : ∀ z :
      (geometricGlobalFunctionalChart A d).ext.Carrier,
      jLeft (pLeft z) = f z.1)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f) :
    ∃ xsX : Fin n → UX,
      ∀ i : Fin n,
        pLeft ((geometricGlobalFunctionalChart A d).ext.rootEmbedding i)
          = iLeft (xsX i) := by
  classical
  have hExist (i : Fin n) :
      ∃ x : UX, jLeft (iLeft x) = f (d.roots i) := by
    obtain ⟨x, hx⟩ := hRoots ⟨i, rfl⟩
    exact ⟨x, hx⟩
  choose xsX hxs using hExist
  refine ⟨xsX, ?_⟩
  intro i
  apply jLeft.injective
  calc
    jLeft (pLeft
        ((geometricGlobalFunctionalChart A d).ext.rootEmbedding i))
        = f (d.roots i) := hPieceMap _
    _ = jLeft (iLeft (xsX i)) := (hxs i).symm

end AllThoseRamseyClasses.Lifts
