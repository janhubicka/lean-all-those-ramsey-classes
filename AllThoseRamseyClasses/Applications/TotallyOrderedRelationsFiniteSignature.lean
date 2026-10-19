import AllThoseRamseyClasses.Applications.TotallyOrderedRelationsRamseyTheorem

/-!
# Totally ordered relations: paper-level theorem for any finite signature

The incidence construction indexes its new vertices by relation
symbols and therefore temporarily chooses a linear order of the
symbols. This is **NOT** additional structure on the objects of
the paper's Ramsey class.

Since the relational signature is finite, choose an arbitrary
linear order of its symbol type using an equivalence with `Fin n`,
apply the fully source-matched incidence Ramsey theorem, and
forget this auxiliary choice from the final statement.

This completes exactly the symbol-order bookkeeping needed to
express the manuscript's `thm:TO` with **no externally supplied
order on relation symbols**. Positive relation instances remain
genuinely linearly ordered as required; zero-arity relation
symbols and the empty language are included.

The proof relies on the full finite theorem in the sibling module,
whose complete Lean/axiom audit must pass separately before this
becomes a published verification endpoint.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- Finite Ramsey property of genuinely totally ordered relational
structures for *every* finite relational signature, without
requiring any **given** order on its relation-symbol type.

The target has an actual linear order of vertices and actual
linear orders of each positive relation-instance subtype, and
the arrow uses full induced embeddings of the literal doubled-arity
relational language `L,2L`. -/
theorem genuinelyTotallyOrderedRelations_areRamsey_finiteSignature
    {L : RelLanguage.{u}}
    [Finite L.Symbol]
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
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin L.Symbol
  letI : LinearOrder L.Symbol := LinearOrder.lift' e e.injective
  exact genuinelyTotallyOrderedRelations_areRamsey A B κ

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
