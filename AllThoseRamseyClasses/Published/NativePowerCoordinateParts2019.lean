import PartiteConstruction.Partite.Induced

/-!
# Native coordinate retractions agree after the original part projection

A minimal transverse Hales--Jewett family has a parameter coordinate
on each one-line-deletion rest, but the exceptional line can require a
DIFFERENT parameter coordinate. The resulting two coordinate
evaluation maps into the old picture need not agree vertexwise.

The actual native partite power provides a weaker unconditional
compatibility: ALL coordinate evaluations of any one core vertex
have the SAME old part label. This follows directly from the
definition of a real power vertex, not from any hypothetical
completion or part-labelled target.

For an Old picture with selected support alpha:Q↪P, the common
original part is alpha(z.part). Therefore even when coordinate
evaluation at k and at l return different vertices of Old, their
images have identical part label in P.

The result is necessary boundary data for a future two-map
amalgamation argument, but NOT sufficient to construct a common
closed K-boundary: equality of part labels does not imply
equality of vertices or give an embedding of the entire root
into a single A-copy. The high-rank multi-line theorem remains
open, and no root is incorrectly declared closed.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Partite
open StructuralRamsey.Partite.Induced

universe u v
variable {L : RelLanguage.{u}} {P Q V X : Type v}

/-- The old outer part of any chosen coordinate of the native
power of an EXACT selected-support restriction is determined
by the power vertex's own restricted part, independently
of the coordinate. -/
theorem nativePower_selected_coordinate_old_part
    (Old : System L P V) (alpha : Q ↪ P)
    (N : ℕ) (z : NonInduced.Vertex (Old.restrict alpha) N)
    (k : Fin N) :
    Old.part (z.coord k).1 = alpha z.part := by
  calc
    Old.part (z.coord k).1 =
        alpha ((Old.restrict alpha).part (z.coord k)) :=
      (Old.restrictedPart_spec alpha (z.coord k)).symm
    _ = alpha z.part :=
      congrArg alpha (z.belongs k)

/-- Any two coordinate evaluations of the SAME genuine native
power core vertex agree on their image in the OLD outer part
set, even though the evaluated old vertices may be different. -/
theorem nativePower_two_coordinates_old_parts_agree
    (Old : System L P V) (alpha : Q ↪ P)
    (N : ℕ) (z : NonInduced.Vertex (Old.restrict alpha) N)
    (k l : Fin N) :
    Old.part (z.coord k).1 = Old.part (z.coord l).1 :=
  (nativePower_selected_coordinate_old_part Old alpha N z k).trans
    (nativePower_selected_coordinate_old_part Old alpha N z l).symm

/-- The same old-part compatibility holds pointwise on any fully
embedded exact source test inside the genuine native power core.
There is NO assertion that the two coordinate evaluations embed
the whole test or coincide as vertices. -/
theorem nativePower_embedded_core_coordinate_parts_agree
    (Old : System L P V) (alpha : Q ↪ P)
    (N : ℕ)
    (Test : RelStructure L X)
    (e : RelStructure.Embedding Test
      (power (Old.restrict alpha) N).toRelStructure)
    (k l : Fin N) (x : X) :
    Old.part ((e x).coord k).1 =
      Old.part ((e x).coord l).1 :=
  nativePower_two_coordinates_old_parts_agree Old alpha N (e x) k l

end AllThoseRamseyClasses.Published
