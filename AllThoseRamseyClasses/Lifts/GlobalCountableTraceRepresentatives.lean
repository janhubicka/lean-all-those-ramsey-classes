import AllThoseRamseyClasses.Lifts.GlobalFiniteSignatureAgeCount

/-!
# Track F: countably many representatives of original regular maximal traces

For a finite old relation/function signature and regular F,
the actual hereditary age of original ROOT-INJECTIVE maximal traces
has finitely many members on every fixed labelled carrier Fin n.
We now assemble a countable disjoint union of these finite fibres.

Every original finite maximal-trace age member on ANY finite carrier
is FULLY isomorphic to a representative on Fin n. The isomorphism is
a genuinely FULL functional embedding: it reflects all added
relations and preserves COMPLETE set-valued old function fibres.
It uses a general functional-structure relabelling along an Equiv,
not an unjustified weak source quotient.

This provides the exact "countably many isomorphism types" prerequisite
in the finite-native-signature regular case of the printed Section 3
Fraisse argument, independently of Claim 2 or strong AP.

No Fraisse limit, omega-categoricity, existential completeness or
Ramsey theorem is asserted here. The native signature being finite
is essential for this counting argument; regularity alone says only
that extra lift symbols have finite arity fibres.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w

/-- Pull a full set-valued functional structure back across an
actual equivalence of carriers. Every relation truth value and
whole function-value fibre is transported, including nullaries. -/
def functionalStructureRelabel
    {L : Language.{u}} {V : Type v} {W : Type w}
    (Y : Structure L V) (e : W ≃ V) : Structure L W where
  rel := fun R xs => Y.rel R (e ∘ xs)
  func := fun f xs => {z | e z ∈ Y.func f (e ∘ xs)}

/-- The bijection from the relabelled carrier to the original one
is a FULL functional embedding, not merely a weak homomorphism. -/
def functionalStructureRelabelEmbedding
    {L : Language.{u}} {V : Type v} {W : Type w}
    (Y : Structure L V) (e : W ≃ V) :
    Structure.Embedding (functionalStructureRelabel Y e) Y where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R xs
    exact Iff.rfl
  map_func := by
    intro f xs
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := e.surjective y
      exact ⟨x, hy, rfl⟩

/-- Every member of the ACTUAL hereditary original global
maximal-trace age is fully isomorphic to a member on Fin n,
with its complete native functional fibres and distinct-root
added relations intact. No regularity assumption is needed. -/
theorem globalMaximalTraceAge_exists_finRepresentative
    {L : Language.{u}}
    (F K : ∀ {W : Type}, Structure L W → Prop)
    {V : Type}
    (Y : Structure (globalFunctionalPieceLanguage F) V)
    (hY : IsGlobalFiniteMaximalTrace F K Y) :
    ∃ (n : ℕ)
      (Z : Structure (globalFunctionalPieceLanguage F) (Fin n)),
      IsGlobalFiniteMaximalTrace F K Z ∧
        ∃ (e : Structure.Embedding Z Y), Function.Surjective e := by
  classical
  letI : Finite V := hY.1
  letI : Fintype V := Fintype.ofFinite V
  let e : Fin (Fintype.card V) ≃ V :=
    (Fintype.equivFin V).symm
  let Z : Structure (globalFunctionalPieceLanguage F)
      (Fin (Fintype.card V)) :=
    functionalStructureRelabel Y e
  let j : Structure.Embedding Z Y :=
    functionalStructureRelabelEmbedding Y e
  exact ⟨Fintype.card V, Z,
    IsGlobalFiniteMaximalTrace.of_embedding F K hY j,
    j, e.surjective⟩

/-- A countable set of ACTUAL original maximal-trace representatives:
for each n, its exact full expanded age on Fin n is finite. -/
theorem globalMaximalTraceAge_countable_finRepresentatives
    (L : Language.{u})
    (F K : ∀ {W : Type}, Structure L W → Prop)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hRegular : GlobalFunctionalPieceRegular F) :
    Countable
      (Σ n : ℕ,
        {Z : Structure (globalFunctionalPieceLanguage F) (Fin n) //
          IsGlobalFiniteMaximalTrace F K Z}) := by
  classical
  letI (n : ℕ) : Finite
      {Z : Structure (globalFunctionalPieceLanguage F) (Fin n) //
        IsGlobalFiniteMaximalTrace F K Z} :=
    globalMaximalTraceAge_finite_onFiniteCarrier
      L F K hRegular (Fin n)
  infer_instance

/-- A concrete countable type of genuine representatives that
covers EVERY full isomorphism type of original regular maximal
global traces on arbitrary finite carriers.

This is a countability certificate without quotienting by an
unformalized isomorphism relation. The displayed embedding is
surjective AND full. No strong AP, JEP or Ramsey assumptions. -/
theorem globalMaximalTraceAge_countableIsoCover
    (L : Language.{u})
    (F K : ∀ {W : Type}, Structure L W → Prop)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hRegular : GlobalFunctionalPieceRegular F) :
    Countable
      (Σ n : ℕ,
        {Z : Structure (globalFunctionalPieceLanguage F) (Fin n) //
          IsGlobalFiniteMaximalTrace F K Z}) ∧
    ∀ {V : Type}
      (Y : Structure (globalFunctionalPieceLanguage F) V)
      (hY : IsGlobalFiniteMaximalTrace F K Y),
      ∃ p : Σ n : ℕ,
        {Z : Structure (globalFunctionalPieceLanguage F) (Fin n) //
          IsGlobalFiniteMaximalTrace F K Z},
        ∃ e : Structure.Embedding p.2.1 Y,
          Function.Surjective e := by
  refine ⟨globalMaximalTraceAge_countable_finRepresentatives
    L F K hRegular, ?_⟩
  intro V Y hY
  obtain ⟨n, Z, hZ, e, he⟩ :=
    globalMaximalTraceAge_exists_finRepresentative F K Y hY
  exact ⟨⟨n, ⟨Z, hZ⟩⟩, e, he⟩

end AllThoseRamseyClasses.Lifts
