import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceDecodedOldData

/-!
# Complete positive-tuple order axioms of the decoded weak incidence target

The arbitrary weak auxiliary Ramsey witness need not be a canonical lift,
nor must its INTERNAL paper order be linear.  The decoded Old structure
uses a genuine linear order on the positive tuples of each relation
symbol, pulled back from the lexicographic (singleton tag, input tuple)
key of the EXTERNAL ordered witness.

These source-matched lemmas record reflexivity, transitivity and
antisymmetry of the decoded tuple comparisons, complementing the
already proved positivity support and totality.  All are restricted
to positive instances, as in the manuscript's ordering of R_r(A).
No false global injectivity assumption on function outputs is used.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v

theorem weakDecoded_tupleOrder_refl_of_positive
    {L : RelLanguage.{u}} {W : Type v} [LinearOrder W]
    (C : Structure (markedIncidencePaperLanguage L) W)
    (hC : IncidenceFunctionLaws C)
    (r : L.Symbol)
    (t : Fin (L.arity r) → WeakOldVertices C)
    (ht : (weakDecodedTotalOrderData C hC).base.rel r t) :
    (weakDecodedTotalOrderData C hC).tupleLE r t t := by
  letI : LinearOrder (WeakPositiveTuples C r) :=
    weakPositiveTuplesLinearOrder hC r
  exact ⟨ht, ht,
    @le_refl (WeakPositiveTuples C r)
      (weakPositiveTuplesLinearOrder hC r).toPreorder
      (weakOldPositiveTuple C r t ht)⟩

theorem weakDecoded_tupleOrder_trans
    {L : RelLanguage.{u}} {W : Type v} [LinearOrder W]
    (C : Structure (markedIncidencePaperLanguage L) W)
    (hC : IncidenceFunctionLaws C)
    (r : L.Symbol)
    (t s q : Fin (L.arity r) → WeakOldVertices C)
    (hts : (weakDecodedTotalOrderData C hC).tupleLE r t s)
    (hsq : (weakDecodedTotalOrderData C hC).tupleLE r s q) :
    (weakDecodedTotalOrderData C hC).tupleLE r t q := by
  rcases hts with ⟨ht, hs, hleTS⟩
  rcases hsq with ⟨hs', hq, hleSQ⟩
  letI : LinearOrder (WeakPositiveTuples C r) :=
    weakPositiveTuplesLinearOrder hC r
  have hSame : weakOldPositiveTuple C r s hs =
      weakOldPositiveTuple C r s hs' := by
    apply Subtype.ext
    rfl
  rw [hSame] at hleTS
  exact ⟨ht, hq,
    @le_trans (WeakPositiveTuples C r)
      (weakPositiveTuplesLinearOrder hC r).toPreorder
      (weakOldPositiveTuple C r t ht)
      (weakOldPositiveTuple C r s hs')
      (weakOldPositiveTuple C r q hq)
      hleTS hleSQ⟩

theorem weakDecoded_tupleOrder_antisymm
    {L : RelLanguage.{u}} {W : Type v} [LinearOrder W]
    (C : Structure (markedIncidencePaperLanguage L) W)
    (hC : IncidenceFunctionLaws C)
    (r : L.Symbol)
    (t s : Fin (L.arity r) → WeakOldVertices C)
    (hts : (weakDecodedTotalOrderData C hC).tupleLE r t s)
    (hst : (weakDecodedTotalOrderData C hC).tupleLE r s t) :
    t = s := by
  rcases hts with ⟨ht, hs, hleTS⟩
  rcases hst with ⟨hs', ht', hleST⟩
  letI : LinearOrder (WeakPositiveTuples C r) :=
    weakPositiveTuplesLinearOrder hC r
  have hSameS : weakOldPositiveTuple C r s hs' =
      weakOldPositiveTuple C r s hs := by
    apply Subtype.ext
    rfl
  have hSameT : weakOldPositiveTuple C r t ht' =
      weakOldPositiveTuple C r t ht := by
    apply Subtype.ext
    rfl
  rw [hSameS, hSameT] at hleST
  have hp : weakOldPositiveTuple C r t ht =
      weakOldPositiveTuple C r s hs :=
    @le_antisymm (WeakPositiveTuples C r)
      (weakPositiveTuplesLinearOrder hC r).toPartialOrder
      (weakOldPositiveTuple C r t ht)
      (weakOldPositiveTuple C r s hs)
      hleTS hleST
  have hTuple : (fun i => (t i).val) = (fun i => (s i).val) :=
    congrArg (fun a : WeakPositiveTuples C r => a.val) hp
  funext i
  exact Subtype.ext (congrFun hTuple i)

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
