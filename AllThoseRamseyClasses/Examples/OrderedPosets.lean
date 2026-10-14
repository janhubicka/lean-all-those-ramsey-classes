import AllThoseRamseyClasses.ApplicationsAPI

/-!
# A completely discharged Ramsey-class example

The finite posets with a named linear extension are Ramsey.
This is a proof, not a conditional application blueprint: the
class's exact weak-subset local-completion property and actual strong
amalgamation are supplied by imported theorems.
-/
namespace AllThoseRamseyClasses.Examples

open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Applications.OrderedPosets

example : FiniteRamseyClass orderedPosetClass :=
  orderedPoset_isRamsey

end AllThoseRamseyClasses.Examples
