import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceOutputKeyOrder
import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceCopywiseLexOrder
import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceWeakOldProjection

/-!
# Exact original copies from arbitrary ordered weak incidence embeddings

The auxiliary freely ordered Ramsey class permits orphan vertices and globally
colliding forward incidence-function outputs.  Nevertheless a FULL ordered
embedding of a canonical source incidence lift A⁺ into a weak witness C
restricts to a full original embedding A -> decoded Old(C):

* Old marking forces the source-original map into Old(C).
* Full relation reflection detects original positive and negative tuples.
* The external order of C restricts to the original vertex order.
* On each embedded canonical A⁺ copy distinct positive incidence tags remain
  distinct, so the tuple-input tie-breaker in decoded target orders vanishes.

The source-only order compatibility hypothesis below is exactly the
choice of a canonical EXTERNAL order on A⁺ (not an assertion about C's
unconstrained internal order predicate). The manuscript source's tuple
comparison is required to be supported on positive instances.

This is the nontrivial copy-decoding lemma of the direct thm:TO proof;
the final Ramsey-arrow construction remains a separate lemma.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- Inside an externally ordered embedded canonical source, the
collision-tolerant decoded positive-tuple order is EXACTLY the source's
given per-relation tuple order. No target global tag injectivity. -/
theorem weakOldPart_positiveTupleLE_iff
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {W : Type w} [LinearOrder W]
    (A : TotalOrderData L U)
    (C : Structure (markedIncidencePaperLanguage L) W)
    (hC : IncidenceFunctionLaws C)
    (e : Structure.Embedding (markedIncidencePaperStructure A) C)
    (hOrdered : ∀ x y : IncidenceCarrier A,
      paperIncidenceLE A x y ↔ e x ≤ e y)
    (r : L.Symbol) (t s : Fin (L.arity r) → U)
    (ht : A.base.rel r t) (hs : A.base.rel r s) :
    (weakDecodedTotalOrderData C hC).tupleLE r
      (weakOldPart A C e ∘ t) (weakOldPart A C e ∘ s) ↔
      A.tupleLE r t s := by
  classical
  let f := weakOldPart A C e
  have htD : (weakOldRelStructure C).rel r (f ∘ t) :=
    (weakOldPart_originalRel_iff A C e r t).mpr ht
  have hsD : (weakOldRelStructure C).rel r (f ∘ s) :=
    (weakOldPart_originalRel_iff A C e r s).mpr hs
  let pt : WeakPositiveTuples C r :=
    weakOldPositiveTuple C r (f ∘ t) htD
  let ps : WeakPositiveTuples C r :=
    weakOldPositiveTuple C r (f ∘ s) hsD
  have hTarget :
      (weakDecodedTotalOrderData C hC).tupleLE r (f ∘ t) (f ∘ s) ↔
        @LE.le (WeakPositiveTuples C r)
          (weakPositiveTuplesLinearOrder hC r).toLE pt ps := by
    constructor
    · rintro ⟨ht', hs', hle⟩
      have hpt : weakOldPositiveTuple C r (f ∘ t) ht' = pt := by
        apply Subtype.ext
        rfl
      have hps : weakOldPositiveTuple C r (f ∘ s) hs' = ps := by
        apply Subtype.ext
        rfl
      simpa only [hpt, hps] using hle
    · intro h
      exact ⟨htD, hsD, h⟩
  obtain ⟨htC, hTagT⟩ :=
    weakOutputTag_of_embedded_canonical A C hC e r t ht
  obtain ⟨hsC, hTagS⟩ :=
    weakOutputTag_of_embedded_canonical A C hC e r s hs
  have hTagPt :
      weakOutputTag hC r pt.1 pt.2 =
        e (positiveTag A r t ht) := by
    exact hTagT
  have hTagPs :
      weakOutputTag hC r ps.1 ps.2 =
        e (positiveTag A r s hs) := by
    exact hTagS
  have hSourceLe :
      (e (positiveTag A r t ht) ≤ e (positiveTag A r s hs)) ↔
        A.tupleLE r t s :=
    (hOrdered _ _).symm.trans
      (paperIncidenceLE_positiveTags_iff A r t s ht hs)
  by_cases hts : t = s
  · subst s
    have hpEq : pt = ps := by
      apply Subtype.ext
      rfl
    have hRefl : @LE.le (WeakPositiveTuples C r)
        (weakPositiveTuplesLinearOrder hC r).toLE pt ps := by
      rw [← hpEq]
      exact @le_refl (WeakPositiveTuples C r)
        (weakPositiveTuplesLinearOrder hC r).toPreorder pt
    have hASource : A.tupleLE r t t :=
      hSourceLe.mp (le_refl _)
    exact ⟨fun _ => hASource, fun _ => hTarget.mpr hRefl⟩
  · have hOutputNe : weakOutputTag hC r pt.1 pt.2 ≠
        weakOutputTag hC r ps.1 ps.2 := by
      rw [hTagPt, hTagPs]
      intro heq
      exact canonical_positiveTag_ne_of_ne A r t s ht hs hts
        (e.injective heq)
    have hSourceLt :
        (e (positiveTag A r t ht) < e (positiveTag A r s hs)) ↔
          A.tupleLE r t s := by
      constructor
      · intro hlt
        exact hSourceLe.mp (le_of_lt hlt)
      · intro h
        have hle := hSourceLe.mpr h
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact hlt
        · exact False.elim
            (hOutputNe (hTagPt.trans (heq.trans hTagPs.symm)))
    calc
      (weakDecodedTotalOrderData C hC).tupleLE r (f ∘ t) (f ∘ s) ↔
          @LE.le (WeakPositiveTuples C r)
            (weakPositiveTuplesLinearOrder hC r).toLE pt ps := hTarget
      _ ↔ weakOutputTag hC r pt.1 pt.2 <
          weakOutputTag hC r ps.1 ps.2 :=
        weakPositiveTuples_le_iff_output_lt_of_ne hC r pt ps hOutputNe
      _ ↔ A.tupleLE r t s := by
        rw [hTagPt, hTagPs]
        exact hSourceLt

/-- Arbitrary FULL, externally ordered canonical incidence embeddings
project to original EXACT embeddings into the decoded Old target.
We require only positivity support for source tuple comparisons; all
other exactness comes from the full auxiliary functional embedding. -/
theorem weakOldPart_originalExactIntoDecoded
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {W : Type w} [LinearOrder W]
    (A : TotalOrderData L U)
    (C : Structure (markedIncidencePaperLanguage L) W)
    (hC : IncidenceFunctionLaws C)
    (e : Structure.Embedding (markedIncidencePaperStructure A) C)
    (hOrdered : ∀ x y : IncidenceCarrier A,
      paperIncidenceLE A x y ↔ e x ≤ e y)
    (hSupported : TupleOrdersSupported A) :
    IsExactEmbedding A (weakDecodedTotalOrderData C hC)
      (weakOldPart A C e) := by
  refine ⟨weakOldPart_injective A C e, ?_, ?_, ?_⟩
  · intro r t
    exact weakOldPart_originalRel_iff A C e r t
  · intro x y
    exact weakOldPart_vertexLE_iff A C e hOrdered x y
  · intro r t s
    constructor
    · intro hTarget
      obtain ⟨htD, hsD⟩ :=
        weakDecoded_tupleOrdersSupported C hC r
          (weakOldPart A C e ∘ t)
          (weakOldPart A C e ∘ s) hTarget
      have ht : A.base.rel r t :=
        (weakOldPart_originalRel_iff A C e r t).mp htD
      have hs : A.base.rel r s :=
        (weakOldPart_originalRel_iff A C e r s).mp hsD
      exact (weakOldPart_positiveTupleLE_iff
        A C hC e hOrdered r t s ht hs).mp hTarget
    · intro hSource
      obtain ⟨ht, hs⟩ := hSupported r t s hSource
      exact (weakOldPart_positiveTupleLE_iff
        A C hC e hOrdered r t s ht hs).mpr hSource

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
