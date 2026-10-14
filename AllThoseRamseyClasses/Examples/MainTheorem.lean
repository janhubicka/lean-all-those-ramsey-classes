import AllThoseRamseyClasses.PublicAPI

/-!
# How to apply the validated corrected relational Theorem 2.18

This file is compiled by the main repository's CI along with every
other file under AllThoseRamseyClasses/. It verifies that the exact
example advertised in README.md elaborates, with no hidden
hypotheses or theorem-construction placeholders.
-/

namespace AllThoseRamseyClasses.Examples

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published

universe u v

variable {L : RelLanguage.{u}}

/-- Application pattern: once the exact corrected multiamalgamation
class and the ambient Ramsey/irreducibility assumptions are available,
the unrestricted conclusion follows without a rank-increment premise. -/
example
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (hR : FiniteRamseyClass R)
    (hRIrred : ∀ {X : Type v} (C : RelStructure L X),
      R C → C.Irreducible)
    (hK : IsCoordinated2019MultiamalgamationClass R K rules) :
    FiniteRamseyClass K :=
  coordinated2019_ramsey_by_profile_sparsening R K rules hR hRIrred hK

/-- Alternatively use the packaged exactly corresponding theorem
target, which is a proved proposition, not a conditional API. -/
example :
    Coordinated2019Theorem218Target.{u,v} (L := L) :=
  coordinated2019_theorem218

end AllThoseRamseyClasses.Examples
