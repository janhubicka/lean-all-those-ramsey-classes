import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceMarkedPaperEmbedding

/-!
# Reflection of the original relational and vertex-order reduct

Every FULL embedding of the SORT-MARKED incidence lift lands
on old vertices when applied to old vertices. We prove its
induced old→old injection actually reflects EVERY original
relation tuple, including false tuples, and the original
vertex-order relation.

This is the reverse direction of the basic incidence-lift encoding,
and is a crucial part of the Ramsey copy-forgetting argument:
the selected auxiliary B-copy need not be canonical, but its
restriction to original vertices must be a full original copy.

The per-symbol POSITIVE tuple orders are not yet inferred here:
they require the support (positive-tuple-only) axioms together
with the complete set-valued incidence-function outputs. That is
a separate proof obligation. Neither full incidence strong
amalgamation nor local completion is asserted.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- The underlying old→old injection induced by ANY full marked
incidence embedding preserves and reflects all original L-tuples. -/
theorem markedEmbedding_originalRel_iff
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (e : Structure.Embedding (markedIncidencePaperStructure A)
      (markedIncidencePaperStructure B))
    (r : L.Symbol) (t : Fin (L.arity r) → U) :
    B.base.rel r (markedEmbedding_originalPart A B e ∘ t) ↔
      A.base.rel r t := by
  let f := markedEmbedding_originalPart A B e
  have he : e ∘ (fun i => (Sum.inl (t i) : IncidenceCarrier A)) =
      (fun i => (Sum.inl (f (t i)) : IncidenceCarrier B)) := by
    funext i
    exact markedEmbedding_originalPart_spec A B e (t i)
  have h := e.map_rel_iff (.paper (.original r))
    (fun i => (Sum.inl (t i) : IncidenceCarrier A))
  change liftedOriginalRel B r
      (e ∘ (fun i => (Sum.inl (t i) : IncidenceCarrier A))) ↔
    liftedOriginalRel A r
      (fun i => (Sum.inl (t i) : IncidenceCarrier A)) at h
  rw [he] at h
  exact ((liftedOriginalRel_old B r (f ∘ t)).symm.trans h).trans
    (liftedOriginalRel_old A r t)

/-- The same induced original-part map preserves AND reflects the
original weak vertex comparison, not just positive relations. -/
theorem markedEmbedding_vertexLE_iff
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (e : Structure.Embedding (markedIncidencePaperStructure A)
      (markedIncidencePaperStructure B))
    (x y : U) :
    B.vertexLE (markedEmbedding_originalPart A B e x)
      (markedEmbedding_originalPart A B e y) ↔
    A.vertexLE x y := by
  have h := e.map_rel_iff (.paper .order)
    ![(Sum.inl x : IncidenceCarrier A), Sum.inl y]
  change paperIncidenceLE B (e (.inl x)) (e (.inl y)) ↔
    A.vertexLE x y at h
  rw [markedEmbedding_originalPart_spec A B e x,
      markedEmbedding_originalPart_spec A B e y] at h
  exact h

/-- Any full marked incidence embedding induces a full embedding
of the original relational L-reduct, on EXACTLY the original
source carrier. No assumption of being a canonical incidence
embedding is made. -/
noncomputable def markedEmbedding_originalRelEmbedding
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (e : Structure.Embedding (markedIncidencePaperStructure A)
      (markedIncidencePaperStructure B)) :
    RelStructure.Embedding A.base B.base where
  toFun := markedEmbedding_originalPart A B e
  injective := markedEmbedding_originalPart_injective A B e
  map_rel_iff := by
    intro r t
    exact markedEmbedding_originalRel_iff A B e r t

/-- The original-reduct full embedding is also an order
embedding for the original vertex-order data predicates. -/
theorem markedEmbedding_originalRelEmbedding_vertexLE
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (e : Structure.Embedding (markedIncidencePaperStructure A)
      (markedIncidencePaperStructure B))
    (x y : U) :
    B.vertexLE (markedEmbedding_originalRelEmbedding A B e x)
      (markedEmbedding_originalRelEmbedding A B e y) ↔
    A.vertexLE x y :=
  markedEmbedding_vertexLE_iff A B e x y

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
