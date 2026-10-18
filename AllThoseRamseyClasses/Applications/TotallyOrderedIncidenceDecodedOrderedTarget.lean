import AllThoseRamseyClasses.Applications.TotallyOrderedRelationsSource
import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceDecodedOrderAxioms

/-!
# Decode arbitrary weak incidence witnesses as GENUINE ordered relations

The direct Ramsey transfer builds its target from the Old-marked vertices of
an arbitrary weak orphan-tolerant functional witness. It is important that
the output is not merely an unconstrained TotalOrderData record.

The external Ramsey vertex order restricts to Old(C). For each relation
symbol r, the positive r-tuples of Old(C) inject into the positive tuples
of the original weak witness by forgetting subtype proofs. Pulling back
the already verified collision-safe lexicographic order through this
injection yields a GENUINE LinearOrder on the exact positive tuple subtype.

This constructs an actual OrderedRelations object, independently of any
unconstrained INTERNAL auxiliary binary order, tag collisions or orphans.
The eventual equality with weakDecodedTotalOrderData transfers the proved
Ramsey arrow to this genuine ordered-relation target.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure

universe u v

/-- The entire positive old tuple, regarded as one positive tuple of the
underlying arbitrary weak functional auxiliary structure. -/
def weakOldPositiveInclusion
    {L : RelLanguage.{u}} {W : Type v}
    (C : Structure (markedIncidencePaperLanguage L) W)
    (r : L.Symbol)
    (p : {t : Fin (L.arity r) → WeakOldVertices C //
      (weakOldRelStructure C).rel r t}) :
    WeakPositiveTuples C r :=
  weakOldPositiveTuple C r p.1 p.2

/-- The entire ordered input tuple is retained, so the inclusion of
positive Old tuples is injective, without global tag injectivity. -/
theorem weakOldPositiveInclusion_injective
    {L : RelLanguage.{u}} {W : Type v}
    (C : Structure (markedIncidencePaperLanguage L) W)
    (r : L.Symbol) :
    Function.Injective (weakOldPositiveInclusion C r) := by
  intro p q h
  have hv : (fun i => (p.1 i).val) =
      (fun i => (q.1 i).val) :=
    congrArg (fun a : WeakPositiveTuples C r => a.val) h
  apply Subtype.ext
  funext i
  exact Subtype.ext (congrFun hv i)

/-- Every positive relation subtype in the Old reduct has an actual
linear order, pulled back from the externally ordered weak incidence
witness's collision-safe positive tuple order. -/
noncomputable def weakOldPositiveLinearOrder
    {L : RelLanguage.{u}} {W : Type v} [LinearOrder W]
    (C : Structure (markedIncidencePaperLanguage L) W)
    (hC : IncidenceFunctionLaws C)
    (r : L.Symbol) :
    LinearOrder {t : Fin (L.arity r) → WeakOldVertices C //
      (weakOldRelStructure C).rel r t} := by
  letI : LinearOrder (WeakPositiveTuples C r) :=
    weakPositiveTuplesLinearOrder hC r
  exact LinearOrder.lift' (weakOldPositiveInclusion C r)
    (weakOldPositiveInclusion_injective C r)

/-- Actual finite totally ordered relational data on the Old part of C.
This is the class-membership certificate missing from a bare
TotalOrderData-only Ramsey arrow conclusion. -/
noncomputable def weakDecodedOrderedRelations
    {L : RelLanguage.{u}} {W : Type v} [LinearOrder W]
    (C : Structure (markedIncidencePaperLanguage L) W)
    (hC : IncidenceFunctionLaws C) :
    OrderedRelations L (WeakOldVertices C) where
  base := weakOldRelStructure C
  positiveOrders := weakOldPositiveLinearOrder C hC

/-- The two independently constructed target encodings agree on their
entire relational and vertex/tuple order data, not merely on positive
instances. Thus every arrow obtained using the earlier decoder is
already an arrow into a genuine OrderedRelations witness. -/
theorem weakDecodedOrderedRelations_toTotalOrderData
    {L : RelLanguage.{u}} {W : Type v} [LinearOrder W]
    (C : Structure (markedIncidencePaperLanguage L) W)
    (hC : IncidenceFunctionLaws C) :
    (weakDecodedOrderedRelations C hC).toTotalOrderData =
      weakDecodedTotalOrderData C hC := by
  rfl

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
