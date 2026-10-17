import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceTwoWayCoordinates
import PartiteConstruction.Structure.FreeAmalgam

/-!
# Disjoint incidence sorts survive full functional free amalgamation

To reconstruct the ORIGINAL vertex set and relation-tuple orders from
a freely ordered auxiliary Ramsey witness, it suffices to keep Old
disjoint from every New_r and distinct New_r sorts pairwise disjoint.
No axiom asserts that every vertex is generated or even classified.

We verify that these local unary conditions hold in canonical two-way
incidence lifts, reflect under arbitrary FULL embeddings, and survive
genuine FULL functional free amalgamation. These conditions can be
combined with orphan-tolerant coordinate recovery in a later Ramsey
class without assuming the false heredity of literal canonical lifts.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v

/-- Full-embedding transport of the unary Old predicate. -/
private theorem markedOld_iff
    {L : RelLanguage.{u}} {U V : Type v}
    {A : Structure (twoWayIncidenceLanguage L) U}
    {B : Structure (twoWayIncidenceLanguage L) V}
    (e : Structure.Embedding A B) (x : U) :
    B.rel .old ![e x] ↔ A.rel .old ![x] := by
  have h := e.map_rel_iff (.old) ![x]
  have ht : (e ∘ ![x]) = ![e x] := by
    funext i
    fin_cases i
    rfl
  rw [ht] at h
  exact h

/-- Full-embedding transport of every unary symbol-indexed New_r. -/
private theorem markedNew_iff
    {L : RelLanguage.{u}} {U V : Type v}
    {A : Structure (twoWayIncidenceLanguage L) U}
    {B : Structure (twoWayIncidenceLanguage L) V}
    (e : Structure.Embedding A B) (r : L.Symbol) (x : U) :
    B.rel (.newSymbol r) ![e x] ↔
      A.rel (.newSymbol r) ![x] := by
  have h := e.map_rel_iff (.newSymbol r) ![x]
  have ht : (e ∘ ![x]) = ![e x] := by
    funext i
    fin_cases i
    rfl
  rw [ht] at h
  exact h

/-- Old is disjoint from every symbol-indexed new sort, while
New_r and New_s are disjoint for r ≠ s. Orphan tags are allowed. -/
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

/-- Canonical two-way incidence lifts have correctly disjoint
old and tagged symbol sorts, including nullary relation tags. -/
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
    | inr tag => exact hNe (hr.symm.trans hs)

/-- Sort separation is hereditary under FULL embeddings. -/
theorem SeparatedIncidenceSorts.of_embedding
    {L : RelLanguage.{u}} {U V : Type v}
    {A : Structure (twoWayIncidenceLanguage L) U}
    {B : Structure (twoWayIncidenceLanguage L) V}
    (hB : SeparatedIncidenceSorts B)
    (e : Structure.Embedding A B) :
    SeparatedIncidenceSorts A := by
  refine ⟨?_, ?_⟩
  · intro x r hOld hNew
    exact hB.old_new (e x) r
      ((markedOld_iff e x).mpr hOld)
      ((markedNew_iff e r x).mpr hNew)
  · intro x r s hNe hR hS
    exact hB.new_new (e x) r s hNe
      ((markedNew_iff e r x).mpr hR)
      ((markedNew_iff e s x).mpr hS)

/-- Unary sort separation survives any true FULL functional free
amalgam. Each vertex of the amalgam is covered by a side; all
relevant unary predicates are reflected on that side. -/
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
    · exact hA.old_new a r
        ((markedOld_iff iA a).mp hOld)
        ((markedNew_iff iA r a).mp hNew)
    · exact hB.old_new b r
        ((markedOld_iff iB b).mp hOld)
        ((markedNew_iff iB r b).mp hNew)
  · intro z r s hNe hR hS
    rcases hfree.covers z with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact hA.new_new a r s hNe
        ((markedNew_iff iA r a).mp hR)
        ((markedNew_iff iA s a).mp hS)
    · exact hB.new_new b r s hNe
        ((markedNew_iff iB r b).mp hR)
        ((markedNew_iff iB s b).mp hS)

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
