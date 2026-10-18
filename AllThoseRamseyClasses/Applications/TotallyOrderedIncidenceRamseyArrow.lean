import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceWeakCopyProjection
import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceOrderedCanonicalLift
import AllThoseRamseyClasses.Applications.FunctionalCopywiseArrowTransfer
import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceAuxiliaryRamseyClass

/-!
# The direct finite Ramsey arrow for totally ordered relational instances

This assembles the three independently validated components:
1. the full all-arity functional EHN Ramsey theorem on the orphan-tolerant
   incidence-law class, with an EXTERNAL linear order;
2. exact projection of every auxiliary ordered A⁺/B⁺-copy to the decoded
   Old-part structure with collision-safe positive tuple orders;
3. canonical lifting of every exact original A->B embedding to a FULL
   externally ordered A⁺->B⁺ embedding.

The final colouring argument is the generic reusable
`arrow_of_functional_copy_projection`.

The explicit source hypotheses say their chosen external orders agree with
their own canonical paper incidence comparisons, and the per-relation
comparison predicates are supported on actual positive tuples. These are
the source-order axioms of genuine totally ordered relations and are
NOT assumptions on the arbitrary weak target C.

This is a real Ramsey-arrow theorem for these source interfaces. The
separately checked source CanonicalExternalOrder/OrderedRelations modules
will discharge the order-existence hypotheses for the literal paper
thm:TO endpoint.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- Finite totally ordered relational inputs have a Ramsey witness as
soon as their chosen canonical external lift orders coincide with the
literal paper incidence comparisons. No requirement to lift all decoded
original A-copies, and no global collision prohibition on target tags. -/
theorem totallyOrderedRelations_arrow_of_canonical_orders
    {L : RelLanguage.{u}}
    [LinearOrder L.Symbol] [Finite L.Symbol]
    {U V : Type (max u v)} [Finite U] [Finite V]
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (oA : LinearOrder (IncidenceCarrier A))
    (oB : LinearOrder (IncidenceCarrier B))
    (hOrderA : ∀ x y : IncidenceCarrier A,
      paperIncidenceLE A x y ↔
        @LE.le (IncidenceCarrier A) oA.toLE x y)
    (hOrderB : ∀ x y : IncidenceCarrier B,
      paperIncidenceLE B x y ↔
        @LE.le (IncidenceCarrier B) oB.toLE x y)
    (hSupportA : TupleOrdersSupported A)
    (hSupportB : TupleOrdersSupported B)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type (max u v)) (_ : Finite X)
      (D : TotalOrderData L X),
      StructuralRamsey.Arrow (encode A) (encode B) (encode D) κ := by
  classical
  letI : LinearOrder (IncidenceCarrier A) := oA
  letI : LinearOrder (IncidenceCarrier B) := oB
  letI : Finite (IncidenceCarrier A) := finite_incidenceCarrier A
  letI : Finite (IncidenceCarrier B) := finite_incidenceCarrier B
  obtain ⟨W, hW, orderW, C, hC, hAux⟩ :=
    incidenceLawsClass_freelyOrderedRamsey
      (markedIncidencePaperStructure A)
      (markedIncidencePaperStructure B)
      (canonical_incidenceFunctionLaws A)
      (canonical_incidenceFunctionLaws B)
      κ
  letI : Finite W := hW
  letI : LinearOrder W := orderW
  let D := weakDecodedTotalOrderData C hC
  have hOldFinite : Finite (WeakOldVertices C) :=
    weakOldVertices_finite C

  have orderedReflectionA
      (e : Structure.Embedding
        (markedIncidencePaperStructure A).withLinearOrder
        C.withLinearOrder)
      (x y : IncidenceCarrier A) :
      paperIncidenceLE A x y ↔ e x ≤ e y := by
    have hReflect : (e x ≤ e y) ↔ x ≤ y := by
      rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
      constructor
      · rintro (hlt | heq)
        · exact Or.inl (e.strictMono.lt_iff_lt.mp hlt)
        · exact Or.inr (e.injective heq)
      · rintro (hlt | heq)
        · exact Or.inl (e.strictMono hlt)
        · exact Or.inr (congrArg e heq)
    exact (hOrderA x y).trans hReflect.symm

  have orderedReflectionB
      (e : Structure.Embedding
        (markedIncidencePaperStructure B).withLinearOrder
        C.withLinearOrder)
      (x y : IncidenceCarrier B) :
      paperIncidenceLE B x y ↔ e x ≤ e y := by
    have hReflect : (e x ≤ e y) ↔ x ≤ y := by
      rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
      constructor
      · rintro (hlt | heq)
        · exact Or.inl (e.strictMono.lt_iff_lt.mp hlt)
        · exact Or.inr (e.injective heq)
      · rintro (hlt | heq)
        · exact Or.inl (e.strictMono hlt)
        · exact Or.inr (congrArg e heq)
    exact (hOrderB x y).trans hReflect.symm

  let projectA (e : Structure.Embedding
      (markedIncidencePaperStructure A).withLinearOrder
      C.withLinearOrder) :
      RelStructure.Embedding (encode A) (encode D) := by
    let er : Structure.Embedding (markedIncidencePaperStructure A) C :=
      e.linearOrderReduct
    exact encodeEmbedding A D
      (weakOldPart A C er)
      (weakOldPart_originalExactIntoDecoded A C hC er
        (orderedReflectionA e) hSupportA)

  let projectB (e : Structure.Embedding
      (markedIncidencePaperStructure B).withLinearOrder
      C.withLinearOrder) :
      RelStructure.Embedding (encode B) (encode D) := by
    let er : Structure.Embedding (markedIncidencePaperStructure B) C :=
      e.linearOrderReduct
    exact encodeEmbedding B D
      (weakOldPart B C er)
      (weakOldPart_originalExactIntoDecoded B C hC er
        (orderedReflectionB e) hSupportB)

  let lift (a : RelStructure.Embedding (encode A) (encode B)) :
      Structure.Embedding
        (markedIncidencePaperStructure A).withLinearOrder
        (markedIncidencePaperStructure B).withLinearOrder :=
    markedIncidencePaperOrderedEmbedding A B
      (by intro x y; exact hOrderA x y)
      (by intro x y; exact hOrderB x y)
      a
      (exactEmbedding_of_encodeEmbedding A B a)

  have hCompose
      (b : Structure.Embedding
        (markedIncidencePaperStructure B).withLinearOrder
        C.withLinearOrder)
      (a : RelStructure.Embedding (encode A) (encode B))
      (x : U) :
      projectA (b.comp (lift a)) x = projectB b (a x) := by
    apply Subtype.ext
    rfl

  refine ⟨WeakOldVertices C, hOldFinite, D, ?_⟩
  exact AllThoseRamseyClasses.Applications.arrow_of_functional_copy_projection
    projectA projectB lift hCompose hAux

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
