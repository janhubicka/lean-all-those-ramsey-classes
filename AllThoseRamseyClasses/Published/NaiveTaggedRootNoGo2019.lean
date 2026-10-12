import PartiteConstruction.Ramsey.ClosureDescription2019

/-!
# 2019 Lemma 2.28: a no-go theorem for the printed naive part-language lift

The proof of published Lemma 2.28 replaces a partite system by a
unary-part-predicate expansion. It then describes the lifted closure
description by taking EACH possible tagged expansion of a root, but
leaving the SAME original closure-relation symbol on all new rules.

Under published Definition 2.12 / the formal IsUClosed semantics,
that recipe can be inconsistent: EVERY tuple in a designated relation
has to match the root of EVERY closure rule sharing its symbol.

The first theorem below proves the general contradiction whenever
two rules share the symbol, the first root embeds and no single tuple
can match both prescribed root types.

The second derives this obstruction if no first root vertex can be
simultaneously the image of a root embedding of each rule.
The final corollary captures the usual unary part-predicate case:
the two roots require contradictory membership of their first
vertex in a selected unary predicate P.

The issue is not repaired by adding both root-tagged rules with the
same relation symbol. Instead the root tag must also distinguish
the closure-RELATION symbol, as in the newer experimental
tagged-root construction. The published mathematical prose remains
frozen and this is a negative validation theorem, NOT an
unrestricted 2019 Lemma 2.28 proof.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- Reinterpret a tuple of the first closure symbol as a tuple of the
second, using the explicit equality of their relation symbols.
No source vertices or tuples are changed. -/
def reindexSharedClosureTuple
    (first second : ClosureRule L)
    (hSymbol : first.symbol = second.symbol)
    (t : Fin (L.arity first.symbol) → V) :
    Fin (L.arity second.symbol) → V :=
  fun i => t (Fin.cast (congrArg L.arity hSymbol).symm i)

/-- Transport the actual relation tuple along equality of designated
relation symbols. This independent helper avoids dependent elimination
on the surrounding ClosureRule records. -/
theorem relationTuple_transport_symbol_eq
    (A : RelStructure L V)
    (x y : L.Symbol) (h : x = y)
    (t : Fin (L.arity x) → V)
    (ht : A.rel x t) :
    A.rel y (fun i => t (Fin.cast (congrArg L.arity h).symm i)) := by
  cases h
  exact ht

/-- Two closure rules sharing a symbol cannot BOTH hold if the
first root occurs and no relation tuple extending that root can
match the second root type. This is the exact quantifier order
in the 2019 definition: validity is imposed per rule, not as
a disjunction over permissible root types. -/
theorem not_UClosed_of_shared_symbol_incompatible_roots
    (rules : ClosureDescription L)
    (A : RelStructure L V)
    (first second : ClosureRule L)
    (hFirst : first ∈ rules) (hSecond : second ∈ rules)
    (hSymbol : first.symbol = second.symbol)
    (hRoot : Nonempty (Embedding first.root A))
    (hIncompatible :
      ∀ (t : Fin (L.arity first.symbol) → V),
        first.RootMatches A t →
        ¬ second.RootMatches A
          (reindexSharedClosureTuple first second hSymbol t)) :
    ¬ IsUClosed rules A := by
  intro hClosed
  obtain ⟨e⟩ := hRoot
  obtain ⟨t, ⟨ht, htRoot⟩, _⟩ :=
    (hClosed first hFirst).2 e
  have hFirstMatches : first.RootMatches A t :=
    ⟨e, htRoot⟩
  have hTransferred :
      A.rel second.symbol
        (reindexSharedClosureTuple first second hSymbol t) := by
    exact relationTuple_transport_symbol_eq A
      first.symbol second.symbol hSymbol t ht
  exact hIncompatible t hFirstMatches
    ((hClosed second hSecond).1 _ hTransferred)

/-- If two rules share a designated closure relation but their
root embeddings can NEVER have the same FIRST vertex, then a
structure realizing any copy of the first root cannot be closed
for both rules. This uses positive root sizes from 2019 Definition
2.12; both roots are allowed to have different sizes. -/
theorem not_UClosed_of_shared_symbol_disjoint_first_roots
    (rules : ClosureDescription L)
    (A : RelStructure L V)
    (first second : ClosureRule L)
    (hFirst : first ∈ rules) (hSecond : second ∈ rules)
    (hSymbol : first.symbol = second.symbol)
    (hRoot : Nonempty (Embedding first.root A))
    (hDisjoint :
      ∀ (e : Embedding first.root A) (g : Embedding second.root A),
        e ⟨0, first.rootPositive⟩ ≠
          g ⟨0, second.rootPositive⟩) :
    ¬ IsUClosed rules A := by
  apply not_UClosed_of_shared_symbol_incompatible_roots
    rules A first second hFirst hSecond hSymbol hRoot
  intro t hMatches1 hMatches2
  obtain ⟨e, he⟩ := hMatches1
  obtain ⟨g, hg⟩ := hMatches2
  apply hDisjoint e g
  let i : Fin first.rootSize := ⟨0, first.rootPositive⟩
  let j : Fin second.rootSize := ⟨0, second.rootPositive⟩
  have hIndex :
      Fin.cast (congrArg L.arity hSymbol).symm
        (j.castLE second.rootLE) = i.castLE first.rootLE :=
    Fin.ext rfl
  calc
    e i = t (i.castLE first.rootLE) := (he i).symm
    _ = t (Fin.cast (congrArg L.arity hSymbol).symm
          (j.castLE second.rootLE)) := congrArg t hIndex.symm
    _ = g j := hg j

/-- A unary part label P and its negation on the first root
vertex enforce the disjointness condition automatically.
Thus two differently PART-TAGGED roots cannot coexist as closure
rules for the SAME relation symbol if the first root embeds.
This is exactly the obstruction to the printed Lemma 2.28 lift. -/
theorem not_UClosed_of_shared_symbol_opposite_root_tags
    (rules : ClosureDescription L)
    (A : RelStructure L V)
    (first second : ClosureRule L)
    (hFirst : first ∈ rules) (hSecond : second ∈ rules)
    (hSymbol : first.symbol = second.symbol)
    (hRoot : Nonempty (Embedding first.root A))
    (P : V → Prop)
    (hPartFirst :
      ∀ e : Embedding first.root A, P (e ⟨0, first.rootPositive⟩))
    (hPartSecond :
      ∀ g : Embedding second.root A, ¬ P (g ⟨0, second.rootPositive⟩)) :
    ¬ IsUClosed rules A := by
  apply not_UClosed_of_shared_symbol_disjoint_first_roots
    rules A first second hFirst hSecond hSymbol hRoot
  intro e g heq
  exact hPartSecond g (heq ▸ hPartFirst e)

end AllThoseRamseyClasses.Published
