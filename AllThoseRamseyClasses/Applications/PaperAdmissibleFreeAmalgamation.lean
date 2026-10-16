import AllThoseRamseyClasses.Applications.PaperAdmissibleOnePointTypes
import PartiteConstruction.Ramsey.FreeAmalgamation

/-!
# Admissible one-point-type orders of free-amalgamation classes

An immediate but useful class-level specialization of the
one-point-type copywise Ramsey transfer: any hereditary finite
relational free-amalgamation class remains Ramsey when its members
receive an order admissible for a fixed total order on complete
one-point relational type codes.

The target class reuses exactly the original reduct predicate K,
with a second requirement that its external strict linear order is
type-admissible. Full relation reflection is retained. No functional
closure language, infinite signature restriction, or assumption that
every type occurs in the structure is introduced.

For the full manuscript prop:admisible, the prerequisite that a
free-order expansion be Ramsey can replace free amalgamation;
that more general arrow transfer is already in
PaperAdmissibleOnePointTypes.
-/

namespace AllThoseRamseyClasses.Applications.AdmissibleOrders

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v

/-- Every relational free-amalgamation class admits a Ramsey
expansion by a strict vertex order compatible with any fixed
linear order of the complete one-vertex relational types. -/
theorem admissiblyOrderedFreeAmalgamation_areRamsey
    {L : RelLanguage.{u}}
    (K : StructureClass.{u,v} (L := L))
    (hK : FreeAmalgamationClass K)
    (typeOrder : LinearOrder (OnePointCode L))
    {U V : Type v}
    [Finite U] [Finite V] [LinearOrder U] [LinearOrder V]
    (A : RelStructure L U) (B : RelStructure L V)
    (hA : K A) (hB : K B)
    (_hAord : TypeAdmissible typeOrder A)
    (hBord : TypeAdmissible typeOrder B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : RelStructure L W),
      K C ∧
      @TypeAdmissible L W o typeOrder C ∧
      StructuralRamsey.Arrow A.ordered B.ordered
        (@RelStructure.ordered L W C o.toLT) κ := by
  exact typeAdmissible_arrow_of_freeOrder typeOrder K A B
    hBord κ (FreeAmalgamationClass.orderedRamsey hK A B hA hB κ)

end AllThoseRamseyClasses.Applications.AdmissibleOrders
