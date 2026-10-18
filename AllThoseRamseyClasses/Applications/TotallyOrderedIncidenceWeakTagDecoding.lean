import AllThoseRamseyClasses.Applications.FunctionFibreUtilities
import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceAuxiliaryRamseyClass
import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceMarkedTupleProjection

/-!
# Decode weak auxiliary incidence tags without global injectivity

The fully checked freely ordered orphan-tolerant incidence-law class
permits a collision F_r(t)=F_r(u)={z} for distinct positive tuples.
This does NOT obstruct the Ramsey theorem of the paper: ordering
positive target tuples lexicographically by (output tag, input tuple)
breaks ties, and the tags of positive tuples INSIDE any embedded
canonical A⁺ copy are distinct by injectivity of that embedding.

Here we certify the exact input-to-output bridge for ARBITRARY FULL
auxiliary embeddings, not merely for canonical maps: their positive
source tags map to the uniquely chosen target F_r-output, and two
distinct source tuples have distinct target outputs.

No global injectivity hypothesis on the auxiliary witness is assumed.
Thus this is the source-matched key for the shorter tie-break proof
outlined in the independent 17 October manuscript audit note.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- A positive tuple in a weak auxiliary incidence structure has
one designated singleton output. Its definition uses only the
already verified positive-singleton law, not reverse functions. -/
noncomputable def weakOutputTag
    {L : RelLanguage.{u}} {W : Type w}
    {C : Structure (markedIncidencePaperLanguage L) W}
    (hC : IncidenceFunctionLaws C)
    (r : L.Symbol) (t : Fin (L.arity r) → W)
    (ht : C.rel (.paper (.original r)) t) : W :=
  Classical.choose (hC.positive_singleton r t ht)

/-- The designated output is the ENTIRE forward function fibre. -/
theorem weakOutputTag_fibre
    {L : RelLanguage.{u}} {W : Type w}
    {C : Structure (markedIncidencePaperLanguage L) W}
    (hC : IncidenceFunctionLaws C)
    (r : L.Symbol) (t : Fin (L.arity r) → W)
    (ht : C.rel (.paper (.original r)) t) :
    C.func r t = {weakOutputTag hC r t ht} :=
  (Classical.choose_spec (hC.positive_singleton r t ht)).1

/-- Every canonical positive tuple has exactly its uniquely named
source incidence vertex as its forward set-valued function value. -/
theorem canonical_positiveTag_fibre
    {L : RelLanguage.{u}} {V : Type v}
    (A : TotalOrderData L V)
    (r : L.Symbol) (t : Fin (L.arity r) → V)
    (ht : A.base.rel r t) :
    fullIncidenceFibre A r (fun i => .inl (t i)) =
      {positiveTag A r t ht} := by
  classical
  rw [fullIncidenceFibre_old A r t]
  ext z
  simp [valueFibre, incidenceValue, positiveTag, ht]

/-- A canonical source lift's positive tag, under an ARBITRARY
full auxiliary embedding e, maps to the unique target function
output on the image of the original tuple.

Crucially e need NOT be the canonical extension of an original
embedding: source-tag uniqueness follows from FULL function-fibre
equality, not from a syntactic description of e. -/
theorem weakOutputTag_of_embedded_canonical
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {W : Type w}
    (A : TotalOrderData L U)
    (C : Structure (markedIncidencePaperLanguage L) W)
    (hC : IncidenceFunctionLaws C)
    (e : Structure.Embedding (markedIncidencePaperStructure A) C)
    (r : L.Symbol) (t : Fin (L.arity r) → U)
    (ht : A.base.rel r t) :
    ∃ hPos :
        C.rel (.paper (.original r))
          (e ∘ (fun i => (Sum.inl (t i) : IncidenceCarrier A))),
      weakOutputTag hC r
          (e ∘ (fun i => (Sum.inl (t i) : IncidenceCarrier A)))
          hPos =
        e (positiveTag A r t ht) := by
  classical
  have hSource : liftedOriginalRel A r
      (fun i => (Sum.inl (t i) : IncidenceCarrier A)) :=
    (liftedOriginalRel_old A r t).mpr ht
  have hPos :
      C.rel (.paper (.original r))
        (e ∘ (fun i => (Sum.inl (t i) : IncidenceCarrier A))) :=
    (e.map_rel_iff (.paper (.original r))
      (fun i => (Sum.inl (t i) : IncidenceCarrier A))).mpr hSource
  refine ⟨hPos, ?_⟩
  have hMap := e.map_func r
    (fun i => (Sum.inl (t i) : IncidenceCarrier A))
  change e '' fullIncidenceFibre A r
      (fun i => (Sum.inl (t i) : IncidenceCarrier A)) =
    C.func r
      (e ∘ (fun i => (Sum.inl (t i) : IncidenceCarrier A))) at hMap
  have hTarget :
      C.func r
        (e ∘ (fun i => (Sum.inl (t i) : IncidenceCarrier A))) =
          {e (positiveTag A r t ht)} :=
    FunctionFibreUtilities.singleton_map_of_image
      e hMap (positiveTag A r t ht)
        (canonical_positiveTag_fibre A r t ht)
  have hChosen := weakOutputTag_fibre hC r _ hPos
  exact Set.singleton_eq_singleton_iff.mp (hChosen.symm.trans hTarget)

/-- Distinct source r-tuples have distinct canonical incidence
vertices even if they share coordinates; the TAG contains the
entire positive tuple, not only a support set. -/
theorem canonical_positiveTag_ne_of_ne
    {L : RelLanguage.{u}} {U : Type v}
    (A : TotalOrderData L U) (r : L.Symbol)
    (t s : Fin (L.arity r) → U)
    (ht : A.base.rel r t) (hs : A.base.rel r s)
    (hne : t ≠ s) :
    positiveTag A r t ht ≠ positiveTag A r s hs := by
  intro h
  have hSigma :
      (⟨r, ⟨t, ht⟩⟩ :
        Sigma fun z : L.Symbol =>
          {q : Fin (L.arity z) → U // A.base.rel z q}) =
      ⟨r, ⟨s, hs⟩⟩ :=
    Sum.inr.inj (by simpa only [positiveTag] using h)
  have hts : t = s := by
    simpa only [Sigma.mk.injEq, heq_iff_eq, Subtype.mk.injEq,
      eq_self_iff_true, true_and] using hSigma
  exact hne hts

/-- The designated target tags of distinct positive tuples of
an embedded canonical A⁺-copy are DISTINCT, even if target
positive tuples outside this copy collide globally.

This is precisely why an arbitrary lexicographic tie-break on
source tuple coordinates cannot spoil the induced tuple order
WITHIN the selected B⁺ copy in the Ramsey arrow. -/
theorem weakOutputTags_distinct_on_embedded_canonical
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {W : Type w}
    (A : TotalOrderData L U)
    (C : Structure (markedIncidencePaperLanguage L) W)
    (hC : IncidenceFunctionLaws C)
    (e : Structure.Embedding (markedIncidencePaperStructure A) C)
    (r : L.Symbol) (t s : Fin (L.arity r) → U)
    (ht : A.base.rel r t) (hs : A.base.rel r s)
    (hne : t ≠ s) :
    ∃ (htC :
        C.rel (.paper (.original r))
          (e ∘ (fun i => (Sum.inl (t i) : IncidenceCarrier A))))
      (hsC :
        C.rel (.paper (.original r))
          (e ∘ (fun i => (Sum.inl (s i) : IncidenceCarrier A)))),
      weakOutputTag hC r _ htC ≠ weakOutputTag hC r _ hsC := by
  obtain ⟨htC, htagt⟩ :=
    weakOutputTag_of_embedded_canonical A C hC e r t ht
  obtain ⟨hsC, htags⟩ :=
    weakOutputTag_of_embedded_canonical A C hC e r s hs
  refine ⟨htC, hsC, ?_⟩
  rw [htagt, htags]
  intro heq
  exact canonical_positiveTag_ne_of_ne A r t s ht hs hne
    (e.injective heq)

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
