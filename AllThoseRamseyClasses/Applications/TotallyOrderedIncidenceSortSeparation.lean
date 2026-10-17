import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceTwoWayCoordinates
import PartiteConstruction.Structure.FreeAmalgam

/-!
# Disjoint incidence sorts survive full functional free amalgamation

A freely ordered auxiliary Ramsey witness need not be a literal canonical
incidence lift. To reconstruct an ORIGINAL vertex set and relation-tuple
orders from the tagged witness, it suffices to impose universal local sort
separation: Old is disjoint from every New_r and distinct New_r sorts do
not intersect. No axiom says all vertices are generated or classified.

These sort-separation laws hold in the actual marked two-way incidence
lifts, are reflected under FULL embeddings and survive every genuine
FULL functional free amalgam. Thus they can be combined with the
orphan-tolerant forward and reverse coordinate laws in a future free-
amalgamation Ramsey class, without assuming false canonical-lift heredity.

This is a class-invariant component, not a class-level Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v

/-- Any genuine FULL embedding reflects unary relation symbols
on singleton input tuples, not only positive unary facts. -/
private theorem embedding_unary_iff
    {M : Language.{u}}
    {U V : Type v}
    {A : Structure M U} {B : Structure M V}
    (e : Structure.Embedding A B)
    (R : M.RelSymbol) (x : U)
    (hArity : M.relArity R = 1) :
    B.rel R (fun _ : Fin (M.relArity R) => e x) ↔
      A.rel R (fun _ : Fin (M.relArity R) => x) := by
  have ht : (e ∘ (fun _ : Fin (M.relArity R) => x)) =
      (fun _ : Fin (M.relArity R) => e x) := rfl
  rw [← ht]
  exact e.map_rel_iff R (fun _ => x)

/-- The set of original vertices is disjoint from every tagged sort,
and two distinct relation symbols have disjoint tagged sorts. -/
structure SeparatedIncidenceSorts
    {L : RelLanguage.{u}} {V : Type v}
    (C : Structure (twoWayIncidenceLanguage L) V) : Prop where
  old_new :
    ∀ (x : V) (r : L.Symbol),
      C.rel .old ![x] → ¬ C.rel (.newSymbol r) ![x]
  new_new :
    ∀ (x : V) (r s : L.Symbol),
      r ≠ s →
      C.rel (.newSymbol r) ![x] →
      ¬ C.rel (.newSymbol s) ![x]

/-- Canonical two-way incidence lifts have honest disjoint old
and symbol-indexed new sorts, including nullary relation tags. -/
theorem canonical_separatedIncidenceSorts
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {V : Type v}
    (A : TotalOrderData L V) :
    SeparatedIncidenceSorts (canonicalTwoWayIncidence A) := by
  refine ⟨?_, ?_⟩
  · intro x r hOld hNew
    change isOriginalVertex A x at hOld
    change hasIncidenceSymbol A r x at hNew
    cases x with
    | inl a => exact hNew
    | inr a => exact hOld
  · intro x r s hNe hr hs
    change hasIncidenceSymbol A r x at hr
    change hasIncidenceSymbol A s x at hs
    cases x with
    | inl a => exact hr
    | inr tag =>
        exact hNe (hr.symm.trans hs)

/-- If a target has disjoint unary Old/New_r sorts, every FULL
embedded source has the same separation. -/
theorem SeparatedIncidenceSorts.of_embedding
    {L : RelLanguage.{u}}
    {U V : Type v}
    {A : Structure (twoWayIncidenceLanguage L) U}
    {B : Structure (twoWayIncidenceLanguage L) V}
    (hB : SeparatedIncidenceSorts B)
    (e : Structure.Embedding A B) :
    SeparatedIncidenceSorts A := by
  refine ⟨?_, ?_⟩
  · intro x r hOld hNew
    have hOldB : B.rel .old ![e x] := by
      have h := e.map_rel_iff (.old) ![x]
      have ht : (e ∘ ![x]) = ![e x] := by
        funext i
        fin_cases i
        rfl
      rw [ht] at h
      exact h.mpr hOld
    have hNewB : B.rel (.newSymbol r) ![e x] := by
      have h := e.map_rel_iff (.newSymbol r) ![x]
      have ht : (e ∘ ![x]) = ![e x] := by
        funext i
        fin_cases i
        rfl
      rw [ht] at h
      exact h.mpr hNew
    exact hB.old_new (e x) r hOldB hNewB
  · intro x r s hNe hR hS
    have hRB : B.rel (.newSymbol r) ![e x] := by
      have h := e.map_rel_iff (.newSymbol r) ![x]
      have ht : (e ∘ ![x]) = ![e x] := by
        funext i
        fin_cases i
        rfl
      rw [ht] at h
      exact h.mpr hR
    have hSB : B.rel (.newSymbol s) ![e x] := by
      have h := e.map_rel_iff (.newSymbol s) ![x]
      have ht : (e ∘ ![x]) = ![e x] := by
        funext i
        fin_cases i
        rfl
      rw [ht] at h
      exact h.mpr hS
    exact hB.new_new (e x) r s hNe hRB hSB

/-- Sort separation is preserved under any genuine FULL functional
free amalgam. The witnesses cover every amalgam vertex, and FULL
relation reflection transports all unary claims to one side.
Mixed unary tags cannot arise across the disjoint sides. -/
theorem SeparatedIncidenceSorts.free_amalgam
    {L : RelLanguage.{u}}
    {H E F W : Type v}
    {D : Structure (twoWayIncidenceLanguage L) H}
    {A : Structure (twoWayIncidenceLanguage L) E}
    {B : Structure (twoWayIncidenceLanguage L) F}
    {C : Structure (twoWayIncidenceLanguage L) W}
    {sA : Structure.Embedding D A}
    {sB : Structure.Embedding D B}
    {iA : Structure.Embedding A C}
    {iB : Structure.Embedding B C}
    (hfree : IsFreeAmalgam sA sB iA iB)
    (hA : SeparatedIncidenceSorts A)
    (hB : SeparatedIncidenceSorts B) :
    SeparatedIncidenceSorts C := by
  refine ⟨?_, ?_⟩
  · intro z r hOld hNew
    rcases hfree.covers z with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · have hOldA : A.rel .old ![a] :=
        (by
          have h := iA.map_rel_iff (.old) ![a]
          have ht : (iA ∘ ![a]) = ![iA a] := by
            funext i; fin_cases i; rfl
          rw [ht] at h
          exact h.mp hOld)
      have hNewA : A.rel (.newSymbol r) ![a] := by
        have h := iA.map_rel_iff (.newSymbol r) ![a]
        have ht : (iA ∘ ![a]) = ![iA a] := by
          funext i; fin_cases i; rfl
        rw [ht] at h
        exact h.mp hNew
      exact hA.old_new a r hOldA hNewA
    · have hOldB : B.rel .old ![b] := by
        have h := iB.map_rel_iff (.old) ![b]
        have ht : (iB ∘ ![b]) = ![iB b] := by
          funext i; fin_cases i; rfl
        rw [ht] at h
        exact h.mp hOld
      have hNewB : B.rel (.newSymbol r) ![b] := by
        have h := iB.map_rel_iff (.newSymbol r) ![b]
        have ht : (iB ∘ ![b]) = ![iB b] := by
          funext i; fin_cases i; rfl
        rw [ht] at h
        exact h.mp hNew
      exact hB.old_new b r hOldB hNewB
  · intro z r s hNe hR hS
    rcases hfree.covers z with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · have hRA : A.rel (.newSymbol r) ![a] := by
        have h := iA.map_rel_iff (.newSymbol r) ![a]
        have ht : (iA ∘ ![a]) = ![iA a] := by
          funext i; fin_cases i; rfl
        rw [ht] at h
        exact h.mp hR
      have hSA : A.rel (.newSymbol s) ![a] := by
        have h := iA.map_rel_iff (.newSymbol s) ![a]
        have ht : (iA ∘ ![a]) = ![iA a] := by
          funext i; fin_cases i; rfl
        rw [ht] at h
        exact h.mp hS
      exact hA.new_new a r s hNe hRA hSA
    · have hRB : B.rel (.newSymbol r) ![b] := by
        have h := iB.map_rel_iff (.newSymbol r) ![b]
        have ht : (iB ∘ ![b]) = ![iB b] := by
          funext i; fin_cases i; rfl
        rw [ht] at h
        exact h.mp hR
      have hSB : B.rel (.newSymbol s) ![b] := by
        have h := iB.map_rel_iff (.newSymbol s) ![b]
        have ht : (iB ∘ ![b]) = ![iB b] := by
          funext i; fin_cases i; rfl
        rw [ht] at h
        exact h.mp hS
      exact hB.new_new b r s hNe hRB hSB

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
