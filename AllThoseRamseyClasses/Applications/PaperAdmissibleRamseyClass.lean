import AllThoseRamseyClasses.Applications.PaperAdmissibleOnePointTypes

/-!
# The arbitrary-class admissible-order Ramsey implication

The published 2019 proposition says that adding an admissible order
to K preserves Ramsey whenever adding an arbitrary free vertex order
to K is Ramsey. It does NOT require free amalgamation.

The prior generic type-code theorem proves this copywise for each
Ramsey witness. Here we package the statement with explicit
class-level quantifiers over ALL finite ordered A,B and ALL finite
nonempty colour types. The admissibility condition uses the fixed
order on complete one-point *relational* types, not the inclusion
order of the underlying Boolean diagonal-type record.

This is a fully general RELATIONAL class transfer. The paper also
discusses languages with genuine functions; a separate semantic
one-point-type bridge is required before treating it as a certificate
of every arbitrary-language formulation of prop:admisible.
-/

namespace AllThoseRamseyClasses.Applications.AdmissibleOrders

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w

/-- Every finite ordered pair of K-members admits a finite freely
ordered Ramsey witness, for every finite nonempty colouring type. -/
def HasFreeOrderRamsey
    {L : RelLanguage.{u}}
    (K : StructureClass.{u,v} (L := L)) : Prop :=
  ∀ {U V : Type v} [Finite U] [Finite V]
      [LinearOrder U] [LinearOrder V],
    ∀ (A : RelStructure L U) (B : RelStructure L V),
      K A → K B →
      ∀ (κ : Type w) [Fintype κ] [Nonempty κ],
        ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
          (C : RelStructure L W),
          K C ∧
          StructuralRamsey.Arrow A.ordered B.ordered
            (@RelStructure.ordered L W C o.toLT) κ

/-- Every pair of admissibly ordered K-members has a finite
Ramsey witness belonging to K with its own admissible order.
The source and target order instances are arbitrary fixed choices
compatible with the same global type-code order. -/
def HasTypeAdmissibleRamsey
    {L : RelLanguage.{u}}
    (K : StructureClass.{u,v} (L := L))
    (typeOrder : LinearOrder (OnePointCode L)) : Prop :=
  ∀ {U V : Type v} [Finite U] [Finite V]
      [LinearOrder U] [LinearOrder V],
    ∀ (A : RelStructure L U) (B : RelStructure L V),
      K A → K B →
      TypeAdmissible typeOrder A →
      TypeAdmissible typeOrder B →
      ∀ (κ : Type w) [Fintype κ] [Nonempty κ],
        ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
          (C : RelStructure L W),
          K C ∧
          @TypeAdmissible L W o typeOrder C ∧
          StructuralRamsey.Arrow A.ordered B.ordered
            (@RelStructure.ordered L W C o.toLT) κ

/-- The general relational form of the paper's admissible-order
proposition, with no free-amalgamation assumption and no restriction
on the cardinality of one-point type codes. Full embeddings preserve
all relations and reflected nonrelations. -/
theorem hasTypeAdmissibleRamsey_of_hasFreeOrderRamsey
    {L : RelLanguage.{u}}
    (K : StructureClass.{u,v} (L := L))
    (typeOrder : LinearOrder (OnePointCode L))
    (hK : HasFreeOrderRamsey.{u,v,w} K) :
    HasTypeAdmissibleRamsey.{u,v,w} K typeOrder := by
  intro U V hU hV oU oV A B hA hB _hAord hBord κ hκ hκne
  exact typeAdmissible_arrow_of_freeOrder typeOrder K A B
    hBord κ (hK A B hA hB κ)

end AllThoseRamseyClasses.Applications.AdmissibleOrders
