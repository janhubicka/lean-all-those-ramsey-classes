import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceWeakTagDecoding

/-!
# Copywise lexicographic reconstruction of ordered relation tuples

The orphan-tolerant incidence laws permit two different positive tuples of a
weak auxiliary structure to have the same forward function output.  Hence a
global comparison using only these outputs is not an order on tuples.

Use any tie-break comparison on the old input tuples.  Here we prove the
essential source-matched statement: inside *every* externally ordered full
embedding of a canonical incidence lift, the tag outputs are pairwise distinct.
The lexicographic comparison of (weak output tag, input tuple) therefore agrees
*exactly* with the original per-relation tuple comparison, regardless of the
chosen tie-breaker outside the embedded copy.

No global injectivity of the weak output function, no reverse-coordinate
function, and no assertion about the target's unrestricted INTERNAL comparison
relation is used.  This is a component of the direct Ramsey proof of thm:TO,
not yet the final Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- On positive tuples of a weak incidence structure, compare the singleton
forward outputs first and use a second relation on input tuples only when the
outputs coincide.  The tie-breaker is deliberately arbitrary here. -/
noncomputable def weakPositiveTupleLexLE
    {L : RelLanguage.{u}} {W : Type w} [LinearOrder W]
    {C : Structure (markedIncidencePaperLanguage L) W}
    (hC : IncidenceFunctionLaws C)
    (r : L.Symbol)
    (tieLE : (Fin (L.arity r) → W) → (Fin (L.arity r) → W) → Prop)
    (t s : Fin (L.arity r) → W)
    (ht : C.rel (.paper (.original r)) t)
    (hs : C.rel (.paper (.original r)) s) : Prop :=
  weakOutputTag hC r t ht < weakOutputTag hC r s hs ∨
    (weakOutputTag hC r t ht = weakOutputTag hC r s hs ∧ tieLE t s)

/-- Every full ordered canonical copy has its original tuple order, when
positive target tuples are compared using singleton outputs with any reflexive
tie-breaker.  The target is allowed to identify outputs of tuples *outside*
the given canonical copy.

The source order compatibility hypothesis is exactly the usual choice of
external order on the canonical lift: it agrees with the paper's incidence
order there.  The target external order is arbitrary. -/
theorem weakPositiveTupleLexLE_on_embedded_canonical
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {W : Type w} [LinearOrder W]
    (A : TotalOrderData L U)
    (C : Structure (markedIncidencePaperLanguage L) W)
    (hC : IncidenceFunctionLaws C)
    (e : Structure.Embedding (markedIncidencePaperStructure A) C)
    (hOrdered : ∀ x y : IncidenceCarrier A,
      paperIncidenceLE A x y ↔ e x ≤ e y)
    (r : L.Symbol)
    (tieLE : (Fin (L.arity r) → W) → (Fin (L.arity r) → W) → Prop)
    (hTieRefl : ∀ q, tieLE q q)
    (t s : Fin (L.arity r) → U)
    (ht : A.base.rel r t) (hs : A.base.rel r s) :
    ∃ (htC :
        C.rel (.paper (.original r))
          (e ∘ (fun i => (Sum.inl (t i) : IncidenceCarrier A))))
      (hsC :
        C.rel (.paper (.original r))
          (e ∘ (fun i => (Sum.inl (s i) : IncidenceCarrier A)))),
      weakPositiveTupleLexLE hC r tieLE
        (e ∘ (fun i => (Sum.inl (t i) : IncidenceCarrier A)))
        (e ∘ (fun i => (Sum.inl (s i) : IncidenceCarrier A)))
        htC hsC ↔ A.tupleLE r t s := by
  classical
  obtain ⟨htC, hTagT⟩ :=
    weakOutputTag_of_embedded_canonical A C hC e r t ht
  obtain ⟨hsC, hTagS⟩ :=
    weakOutputTag_of_embedded_canonical A C hC e r s hs
  refine ⟨htC, hsC, ?_⟩
  simp only [weakPositiveTupleLexLE, hTagT, hTagS]
  have hCompare :
      (e (positiveTag A r t ht) ≤ e (positiveTag A r s hs)) ↔
        A.tupleLE r t s :=
    (hOrdered _ _).symm.trans
      (paperIncidenceLE_positiveTags_iff A r t s ht hs)
  constructor
  · rintro (hlt | ⟨heq, _⟩)
    · exact hCompare.mp (le_of_lt hlt)
    · exact hCompare.mp (le_of_eq heq)
  · intro hTuples
    have hle := hCompare.mpr hTuples
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl hlt
    · have hts : t = s := by
        by_contra hne
        exact canonical_positiveTag_ne_of_ne A r t s ht hs hne
          (e.injective heq)
      refine Or.inr ⟨heq, ?_⟩
      subst s
      exact hTieRefl _

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
