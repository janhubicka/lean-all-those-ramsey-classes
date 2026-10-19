import AllThoseRamseyClasses.Applications.TotallyOrderedRelationsSourceIncidenceOrder
import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceRamseyArrow
import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceDecodedOrderedTarget

/-!
# Ramsey theorem for finite totally ordered relational structures

This is the source-matched endpoint for manuscript `thm:TO` in a
FINITE relational language (arbitrary finite symbol arities, including
zero). Objects consist of a genuine linear order of vertices and,
independently for every relation symbol, a genuine linear order on
the subtype of POSITIVE relation instances.

The proof does not assume that the output of the generic weak
functional EHN theorem is itself a canonical incidence lift. Its
orphan-tolerant auxiliary output may contain orphan tags and different
positive tuples may have colliding function-output tags.

Instead, the old-marked part is decoded as an ACTUAL
`OrderedRelations` target: its vertex order is the external Ramsey
order restricted to old vertices; each positive tuple subtype is
linearly ordered by (output-tag, complete original tuple) with the
second key resolving collisions. Every full ordered auxiliary
canonical source copy projects to an exact original copy; canonical
source embeddings lift to FULL externally ordered functional
embeddings. The colouring is transferred by the reusable
`arrow_of_functional_copy_projection` theorem.

Source external-order compatibility is now discharged by the actual
positive-tuple orders, not assumed as an independent oracle. This
theorem is for finite relational languages as in the paper, not a
claim about arbitrary infinite signatures or the separate metric
and function-valued applications.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- An ordinary encoded totally ordered relational structure with
an EXPLICIT externally supplied vertex `LinearOrder`, so the
quantified target can be packaged without any synthetic global
typeclass assumptions. -/
noncomputable def encodedGenuineOrderedRelations
    {L : RelLanguage.{u}} {W : Type v}
    (orderW : LinearOrder W)
    (D : @OrderedRelations L W orderW) :
    RelStructure (ExpandedLanguage L) W := by
  letI : LinearOrder W := orderW
  exact encode D.toTotalOrderData

/-- Genuine full finite Ramsey theorem for every finite relational
language with a fixed linear order of its symbols. Finite source
and target objects have independently ordered vertices and positive
instances of each relation; there is NO source compatibility premise
beyond these genuine orders.

The target D is packaged with its ACTUAL `LinearOrder`, rather
than a raw `TotalOrderData` record. Copies and colouring are full
induced embeddings of the literal `L,2L` relational encoding. -/
theorem genuinelyTotallyOrderedRelations_areRamsey
    {L : RelLanguage.{u}}
    [LinearOrder L.Symbol] [Finite L.Symbol]
    {U V : Type (max u v)}
    [LinearOrder U] [LinearOrder V] [Finite U] [Finite V]
    (A : OrderedRelations L U)
    (B : OrderedRelations L V)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type (max u v)) (_ : Finite W)
      (orderW : LinearOrder W)
      (D : @OrderedRelations L W orderW),
      StructuralRamsey.Arrow
        (encode A.toTotalOrderData) (encode B.toTotalOrderData)
        (encodedGenuineOrderedRelations orderW D) κ := by
  classical
  let DA := A.toTotalOrderData
  let DB := B.toTotalOrderData
  let oA : LinearOrder (IncidenceCarrier DA) :=
    A.canonicalIncidenceOrder
  let oB : LinearOrder (IncidenceCarrier DB) :=
    B.canonicalIncidenceOrder
  letI : LinearOrder (IncidenceCarrier DA) := oA
  letI : LinearOrder (IncidenceCarrier DB) := oB
  -- These sum carriers also have independently synthesized direct
  -- Sum.LE/Sum.LT instances. Override them explicitly so `withLinearOrder`
  -- and ordered-copy reflection use the ACTUAL chosen external EHN order.
  letI : LE (IncidenceCarrier DA) := oA.toLE
  letI : LT (IncidenceCarrier DA) := oA.toLT
  letI : LE (IncidenceCarrier DB) := oB.toLE
  letI : LT (IncidenceCarrier DB) := oB.toLT
  letI : Finite (IncidenceCarrier DA) := finite_incidenceCarrier DA
  letI : Finite (IncidenceCarrier DB) := finite_incidenceCarrier DB

  obtain ⟨W, hW, orderW, C, hC, hAux⟩ :=
    incidenceLawsClass_freelyOrderedRamsey
      (markedIncidencePaperStructure DA)
      (markedIncidencePaperStructure DB)
      (canonical_incidenceFunctionLaws DA)
      (canonical_incidenceFunctionLaws DB) κ
  letI : Finite W := hW
  letI : LinearOrder W := orderW
  let D := weakDecodedOrderedRelations C hC
  have hOldFinite : Finite (WeakOldVertices C) :=
    weakOldVertices_finite C

  have orderedReflectionA
      (e : Structure.Embedding
        (markedIncidencePaperStructure DA).withLinearOrder
        C.withLinearOrder)
      (x y : IncidenceCarrier DA) :
      paperIncidenceLE DA x y ↔ e x ≤ e y := by
    have hReflect : (e x ≤ e y) ↔ x ≤ y := by
      simp only [le_iff_lt_or_eq]
      constructor
      · rintro (hlt | heq)
        · exact Or.inl (e.strictMono.lt_iff_lt.mp hlt)
        · exact Or.inr (e.injective heq)
      · rintro (hlt | heq)
        · exact Or.inl (e.strictMono hlt)
        · exact Or.inr (congrArg e heq)
    exact (A.canonicalIncidenceOrder_agrees x y).trans hReflect.symm

  have orderedReflectionB
      (e : Structure.Embedding
        (markedIncidencePaperStructure DB).withLinearOrder
        C.withLinearOrder)
      (x y : IncidenceCarrier DB) :
      paperIncidenceLE DB x y ↔ e x ≤ e y := by
    have hReflect : (e x ≤ e y) ↔ x ≤ y := by
      simp only [le_iff_lt_or_eq]
      constructor
      · rintro (hlt | heq)
        · exact Or.inl (e.strictMono.lt_iff_lt.mp hlt)
        · exact Or.inr (e.injective heq)
      · rintro (hlt | heq)
        · exact Or.inl (e.strictMono hlt)
        · exact Or.inr (congrArg e heq)
    exact (B.canonicalIncidenceOrder_agrees x y).trans hReflect.symm

  let projectA (e : Structure.Embedding
      (markedIncidencePaperStructure DA).withLinearOrder
      C.withLinearOrder) :
      RelStructure.Embedding (encode DA) (encode D.toTotalOrderData) := by
    let er : Structure.Embedding (markedIncidencePaperStructure DA) C :=
      e.linearOrderReduct
    exact encodeEmbedding DA D.toTotalOrderData
      (weakOldPart DA C er)
      (weakOldPart_originalExactIntoDecoded DA C hC er
        (orderedReflectionA e) A.tupleOrdersSupported)

  let projectB (e : Structure.Embedding
      (markedIncidencePaperStructure DB).withLinearOrder
      C.withLinearOrder) :
      RelStructure.Embedding (encode DB) (encode D.toTotalOrderData) := by
    let er : Structure.Embedding (markedIncidencePaperStructure DB) C :=
      e.linearOrderReduct
    exact encodeEmbedding DB D.toTotalOrderData
      (weakOldPart DB C er)
      (weakOldPart_originalExactIntoDecoded DB C hC er
        (orderedReflectionB e) B.tupleOrdersSupported)

  let lift (a : RelStructure.Embedding (encode DA) (encode DB)) :
      Structure.Embedding
        (markedIncidencePaperStructure DA).withLinearOrder
        (markedIncidencePaperStructure DB).withLinearOrder :=
    markedIncidencePaperOrderedEmbedding DA DB
      (by intro x y; exact A.canonicalIncidenceOrder_agrees x y)
      (by intro x y; exact B.canonicalIncidenceOrder_agrees x y)
      a (exactEmbedding_of_encodeEmbedding DA DB a)

  have hCompose
      (b : Structure.Embedding
        (markedIncidencePaperStructure DB).withLinearOrder
        C.withLinearOrder)
      (a : RelStructure.Embedding (encode DA) (encode DB))
      (x : U) :
      projectA (b.comp (lift a)) x = projectB b (a x) := by
    apply Subtype.ext
    rfl

  refine ⟨WeakOldVertices C, hOldFinite,
    (inferInstance : LinearOrder (WeakOldVertices C)),
    D, ?_⟩
  change StructuralRamsey.Arrow (encode DA) (encode DB)
    (encode (weakDecodedTotalOrderData C hC)) κ
  exact AllThoseRamseyClasses.Applications.arrow_of_functional_copy_projection
    projectA projectB lift hCompose hAux

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
