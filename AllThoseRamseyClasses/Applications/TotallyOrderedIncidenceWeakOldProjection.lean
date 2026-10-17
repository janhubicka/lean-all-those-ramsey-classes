import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceWeakTagDecoding

/-!
# Project arbitrary full incidence embeddings to a genuine old relational copy

An arbitrary Ramsey-selected full embedding from the canonical marked
incidence lift A⁺ into a WEAK auxiliary structure C need not arise as the
canonical extension of an old map, nor need C itself be any canonical lift.

The unary Old marker still forces the entire source-old carrier into the
subtype of Old-marked target vertices.  We construct an ACTUAL full
relational embedding A -> Old(C) and reflect ALL original positive and
negative relation tuples.  The target's unrestricted internal order and
orphan incidence tags are irrelevant.

A separate theorem transfers the old-vertex order whenever the EXTERNAL
Ramsey order is compatible with the source canonical old-first order.
Together with copywise positive tuple-order recovery, this is the
embedding-projection part of the direct thm:TO Ramsey argument.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- Old-marked vertices of an arbitrary, possibly orphan-containing,
functional auxiliary incidence structure.  The marked sorts need NOT form
a global partition for this subtype to exist. -/
abbrev WeakOldVertices
    {L : RelLanguage.{u}} {W : Type w}
    (C : Structure (markedIncidencePaperLanguage L) W) :=
  {x : W // C.rel (.old) ![x]}

/-- Literal original relational reduct on only Old-marked vertices. -/
def weakOldRelStructure
    {L : RelLanguage.{u}} {W : Type w}
    (C : Structure (markedIncidencePaperLanguage L) W) :
    RelStructure L (WeakOldVertices C) where
  rel r t := C.rel (.paper (.original r)) (fun i => (t i).val)

/-- The image of an original vertex under ANY full marked incidence
embedding lies in the Old-marked subtype of the arbitrary target. -/
noncomputable def weakOldPart
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {W : Type w}
    (A : TotalOrderData L U)
    (C : Structure (markedIncidencePaperLanguage L) W)
    (e : Structure.Embedding (markedIncidencePaperStructure A) C)
    (x : U) : WeakOldVertices C := by
  refine ⟨e (.inl x), ?_⟩
  have hSource :
      (markedIncidencePaperStructure A).rel (.old)
        ![(Sum.inl x : IncidenceCarrier A)] := by
    change isOriginalVertex A (.inl x)
    trivial
  have hMapped := (e.map_rel_iff (.old)
      ![(Sum.inl x : IncidenceCarrier A)]).mpr hSource
  have hTuple :
      (e ∘ ![(Sum.inl x : IncidenceCarrier A)]) =
        ![e (Sum.inl x)] := by
    funext i
    fin_cases i
    rfl
  change C.rel (.old)
      (e ∘ ![(Sum.inl x : IncidenceCarrier A)]) at hMapped
  rw [hTuple] at hMapped
  exact hMapped

/-- The selected old part is injective, because the full incidence
embedding was injective on its entire carrier. -/
theorem weakOldPart_injective
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {W : Type w}
    (A : TotalOrderData L U)
    (C : Structure (markedIncidencePaperLanguage L) W)
    (e : Structure.Embedding (markedIncidencePaperStructure A) C) :
    Function.Injective (weakOldPart A C e) := by
  intro x y hxy
  have heq : e (.inl x) = e (.inl y) :=
    congrArg (fun z : WeakOldVertices C => z.val) hxy
  exact Sum.inl.inj (e.injective heq)

/-- Exact reflection of original r-tuples, including ALL negative
tuples, under the selected Old restriction of an arbitrary full
auxiliary embedding. -/
theorem weakOldPart_originalRel_iff
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {W : Type w}
    (A : TotalOrderData L U)
    (C : Structure (markedIncidencePaperLanguage L) W)
    (e : Structure.Embedding (markedIncidencePaperStructure A) C)
    (r : L.Symbol) (t : Fin (L.arity r) → U) :
    (weakOldRelStructure C).rel r (weakOldPart A C e ∘ t) ↔
      A.base.rel r t := by
  change C.rel (.paper (.original r))
    (e ∘ (fun i => (Sum.inl (t i) : IncidenceCarrier A))) ↔
      A.base.rel r t
  have h := e.map_rel_iff (.paper (.original r))
    (fun i => (Sum.inl (t i) : IncidenceCarrier A))
  change C.rel (.paper (.original r))
      (e ∘ (fun i => (Sum.inl (t i) : IncidenceCarrier A))) ↔
    liftedOriginalRel A r
      (fun i => (Sum.inl (t i) : IncidenceCarrier A)) at h
  exact h.trans (liftedOriginalRel_old A r t)

/-- A genuine full relational embedding into the Old subtype of ANY
auxiliary weak witness, not a map to a hypothesized canonical target. -/
noncomputable def weakOldPart_originalEmbedding
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {W : Type w}
    (A : TotalOrderData L U)
    (C : Structure (markedIncidencePaperLanguage L) W)
    (e : Structure.Embedding (markedIncidencePaperStructure A) C) :
    RelStructure.Embedding A.base (weakOldRelStructure C) where
  toFun := weakOldPart A C e
  injective := weakOldPart_injective A C e
  map_rel_iff := by
    intro r t
    exact weakOldPart_originalRel_iff A C e r t

/-- When the ordered full embedding preserves the EXTERNAL Ramsey
linear order, its Old restriction reflects the original vertex order. -/
theorem weakOldPart_vertexLE_iff
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {W : Type w} [LinearOrder W]
    (A : TotalOrderData L U)
    (C : Structure (markedIncidencePaperLanguage L) W)
    (e : Structure.Embedding (markedIncidencePaperStructure A) C)
    (hOrdered : ∀ x y : IncidenceCarrier A,
      paperIncidenceLE A x y ↔ e x ≤ e y)
    (x y : U) :
    (weakOldPart A C e x).val ≤ (weakOldPart A C e y).val ↔
      A.vertexLE x y := by
  change e (.inl x) ≤ e (.inl y) ↔ A.vertexLE x y
  exact (hOrdered (.inl x) (.inl y)).symm

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
