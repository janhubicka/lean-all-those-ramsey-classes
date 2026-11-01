import AllThoseRamseyClasses.Lifts.RetainedInteriorRootPath
import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram

/-!
# The actual geometric source has the private-component geometry needed
# by the Track A retained-interior path theorem

The original 2019 selected piece is not an arbitrary pair of full
functional root extensions. It is the *complete closed cut together
with one actual Gaifman component*, with an exact induced functional
structure on this carrier. Its standard Fin n root includes ALL
vertices of the closed cut.

Here we instantiate the genuine full free-amalgam decomposition
`geometricGlobalSource_freeDiagram` without imposing an artificial
inner-private connectivity hypothesis. Every vertex on the left
piece that is not in its root is literally in the selected connected
component of the original forbidden source after removing the full
root. This remains true with arbitrary-arity native partial functions
because the root and the piece carrier are complete full substructures.

This is a source-side lemma: no target weak homomorphism-embedding is
assumed injective, no different forbidden source is introduced, and
the old outer cut remains arbitrary. The new opposite boundary and
rooted incompatibility profile are not claimed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V : Type} {n : ℕ}

/-- The actual common inner gluing root, viewed through the FULL
complement inclusion, is precisely the complete ordered root set
of the selected geometric forbidden piece. -/
theorem geometricGlobalSource_innerRoot_range_eq
    (A : Structure L V) (d : GeometricFunctionalPieceData A n) :
    (functionalComponentComplementEmbedding A (Set.range d.roots)
        d.minimal.1 d.left) ''
      Set.range (geometricGlobalComplementChart A d).rootEmbedding =
    Set.range d.roots := by
  ext w
  constructor
  · rintro ⟨b, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(geometricGlobalComplementChart A d).rootEmbedding i,
      ⟨i, rfl⟩, rfl⟩

/-- The private vertices of the genuine selected inner piece are
literally vertices of its selected inner source component.
This discharges `hPrivateInD` from the generic retained-interior
path theorem, once the genuine geometric source chart is selected.
-/
theorem geometricGlobalSource_innerPrivate_in_selectedComponent
    (A : Structure L V) (d : GeometricFunctionalPieceData A n)
    (e : (geometricGlobalFunctionalChart A d).ext.Carrier)
    (he : e ∉ Set.range
      (geometricGlobalFunctionalChart A d).ext.rootEmbedding) :
    e.1 ∈ componentFrom A.graph (Set.range d.roots) d.left := by
  rcases e.2 with hRoot | hD
  · rcases hRoot with ⟨i, hi⟩
    exfalso
    apply he
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hi.symm
  · exact hD

end AllThoseRamseyClasses.Lifts
