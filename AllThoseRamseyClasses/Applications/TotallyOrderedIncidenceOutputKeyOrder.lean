import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceDecodedOldData

/-!
# Compare the decoded positive-instance order with incidence output tags

The target positive-instance order is the linear order pulled back from
(output tag, lexicographically ordered input tuple). Its first-coordinate
comparison is strict whenever the output tags differ. This simple fact is
the missing order-interface bridge for the direct copywise Ramsey transfer.

No global tag injectivity is assumed: different positive tuples can share
the same tag. The last theorem is conditional ONLY on the particular
two outputs being distinct, as happens inside an embedded canonical copy.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure

universe u v

/-- Strictly increasing forward-output tags imply strictly increasing
positive-instance order, independent of any tuple tie-breaker. -/
theorem weakPositiveTuples_lt_of_output_lt
    {L : RelLanguage.{u}} {W : Type v} [LinearOrder W]
    {C : Structure (markedIncidencePaperLanguage L) W}
    (hC : IncidenceFunctionLaws C) (r : L.Symbol)
    (p q : WeakPositiveTuples C r)
    (h : weakOutputTag hC r p.1 p.2 <
      weakOutputTag hC r q.1 q.2) :
    @LT.lt (WeakPositiveTuples C r)
      (weakPositiveTuplesLinearOrder hC r).toLT p q := by
  change weakPositiveTupleKey hC r p < weakPositiveTupleKey hC r q
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- Forward tag strictness implies the decoded non-strict comparison. -/
theorem weakPositiveTuples_le_of_output_lt
    {L : RelLanguage.{u}} {W : Type v} [LinearOrder W]
    {C : Structure (markedIncidencePaperLanguage L) W}
    (hC : IncidenceFunctionLaws C) (r : L.Symbol)
    (p q : WeakPositiveTuples C r)
    (h : weakOutputTag hC r p.1 p.2 <
      weakOutputTag hC r q.1 q.2) :
    @LE.le (WeakPositiveTuples C r)
      (weakPositiveTuplesLinearOrder hC r).toLE p q := by
  change weakPositiveTupleKey hC r p ≤ weakPositiveTupleKey hC r q
  exact le_of_lt (Prod.Lex.toLex_lt_toLex.mpr (Or.inl h))

/-- A decoded comparison cannot reverse a strict comparison between
the designated forward-output tags. -/
theorem weakPositiveTuples_output_le_of_le
    {L : RelLanguage.{u}} {W : Type v} [LinearOrder W]
    {C : Structure (markedIncidencePaperLanguage L) W}
    (hC : IncidenceFunctionLaws C) (r : L.Symbol)
    (p q : WeakPositiveTuples C r)
    (h : @LE.le (WeakPositiveTuples C r)
      (weakPositiveTuplesLinearOrder hC r).toLE p q) :
    weakOutputTag hC r p.1 p.2 ≤
      weakOutputTag hC r q.1 q.2 := by
  change weakPositiveTupleKey hC r p ≤
    weakPositiveTupleKey hC r q at h
  by_contra hn
  have hrev : weakOutputTag hC r q.1 q.2 <
      weakOutputTag hC r p.1 p.2 := lt_of_not_ge hn
  have hrevKey : weakPositiveTupleKey hC r q <
      weakPositiveTupleKey hC r p :=
    Prod.Lex.toLex_lt_toLex.mpr (Or.inl hrev)
  exact (not_lt_of_ge h) hrevKey

/-- When the two output tags are different, decoded comparison is
EXACTLY strict comparison of these output tags; tuple coordinates
play no role. This is the source-matched copywise interface. -/
theorem weakPositiveTuples_le_iff_output_lt_of_ne
    {L : RelLanguage.{u}} {W : Type v} [LinearOrder W]
    {C : Structure (markedIncidencePaperLanguage L) W}
    (hC : IncidenceFunctionLaws C) (r : L.Symbol)
    (p q : WeakPositiveTuples C r)
    (hne : weakOutputTag hC r p.1 p.2 ≠
      weakOutputTag hC r q.1 q.2) :
    (@LE.le (WeakPositiveTuples C r)
      (weakPositiveTuplesLinearOrder hC r).toLE p q) ↔
      weakOutputTag hC r p.1 p.2 <
        weakOutputTag hC r q.1 q.2 := by
  constructor
  · intro h
    have hle := weakPositiveTuples_output_le_of_le hC r p q h
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact False.elim (hne heq)
  · exact weakPositiveTuples_le_of_output_lt hC r p q

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
