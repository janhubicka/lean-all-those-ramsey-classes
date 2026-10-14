import AllThoseRamseyClasses.Applications.OrderedPosetHereditary
import AllThoseRamseyClasses.Published.MinimalRepair4b

/-!
# Corrected closed/irreducible tests enforce the local ordered-poset laws

A weak candidate in the 2019 local-completion axiom need not be
linearly ordered, a poset, or a member of the ambient Ramsey class.
It is therefore incorrect to apply `orderedPosetClass` to the
entire candidate at the start of the local-completion proof.

For the empty closure description all induced tests are closed.
A singleton is automatically ordinary irreducible; the support of
any positive binary tuple is also ordinary irreducible. The exact
corrected membership premise (4b) therefore puts these original
substructures in the ACTUAL ordered-poset class.

This module proves the resulting genuine local laws:
* reflexivity of the partial-order predicate on every vertex;
* compatibility of every nontrivial partial-order edge with the
  positive strict vertex order;
* no positive tuples in the artificial inert auxiliary predicate;
* irreflexivity of the original strict-order predicate.

No global membership or final Ramsey corollary is claimed.
-/

namespace AllThoseRamseyClasses.Applications.OrderedPosets

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published
open AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

private theorem empty_rules_closed {V : Type}
    (A : RelStructure Lang V) :
    IsUClosed (∅ : ClosureDescription Lang) A := by
  intro rule hrule
  exact (Set.not_mem_empty rule hrule).elim

/-- The original exact one-vertex induced test is in K.
No relation on the vertex is needed for the singleton
to be ordinary (hence U-) irreducible. -/
theorem poset_weak_singleton_in_K
    {V : Type} (C : RelStructure Lang V)
    (hTests : CorrectedUIrreduciblesIn
      orderedPosetClass (∅ : ClosureDescription Lang) C)
    (x : V) :
    orderedPosetClass (C.induce ({x} : Set V)) := by
  let S : Set V := {x}
  have hIrr : (C.induce S).Irreducible := by
    intro a b hab
    have hA : a.1 = x := by simpa [S] using a.2
    have hB : b.1 = x := by simpa [S] using b.2
    exact (hab (Subtype.ext (hA.trans hB.symm))).elim
  exact hTests S (empty_rules_closed (C.induce S))
    (hIrr.isUIrreducible (∅ : ClosureDescription Lang))

/-- The exact two-vertex support of ANY positive tuple of the
named binary language is an ordinary irreducible induced seed,
including when its endpoints happen to be equal. -/
theorem poset_weak_binary_seed_in_K
    {V : Type} (C : RelStructure Lang V)
    (hTests : CorrectedUIrreduciblesIn
      orderedPosetClass (∅ : ClosureDescription Lang) C)
    (R : Symbol) (x y : V)
    (hRel : edge C R x y) :
    orderedPosetClass (C.induce ({x, y} : Set V)) := by
  let S : Set V := {x, y}
  let sx : S := ⟨x, by simp [S]⟩
  let sy : S := ⟨y, by simp [S]⟩
  have hTuple : edge (C.induce S) R sx sy :=
    (edge_embedding_iff (inclusion C S) R sx sy).mp hRel
  have hPoint : ∀ t : S, t = sx ∨ t = sy := by
    intro t
    have ht : t.1 = x ∨ t.1 = y := by simpa [S] using t.2
    rcases ht with ht | ht
    · exact Or.inl (Subtype.ext ht)
    · exact Or.inr (Subtype.ext ht)
  have hIrred : (C.induce S).Irreducible := by
    intro a b hab
    rcases hPoint a with ha | ha <;> rcases hPoint b with hb | hb
    · exact (hab (ha.trans hb.symm)).elim
    · subst a
      subst b
      exact ⟨R, ![sx, sy], 0, 1, hTuple, rfl, rfl⟩
    · subst a
      subst b
      exact ⟨R, ![sx, sy], 1, 0, hTuple, rfl, rfl⟩
    · exact (hab (ha.trans hb.symm)).elim
  exact hTests S (empty_rules_closed (C.induce S))
    (hIrred.isUIrreducible (∅ : ClosureDescription Lang))

/-- Every original vertex carries the required reflexive loop in
the source weak partial-order relation, because its singleton
already belongs to the actual class of finite ordered posets. -/
theorem poset_weak_equiv_refl
    {V : Type} (C : RelStructure Lang V)
    (hTests : CorrectedUIrreduciblesIn
      orderedPosetClass (∅ : ClosureDescription Lang) C)
    (x : V) : edge C .equiv x x := by
  let S : Set V := {x}
  let sx : S := ⟨x, by simp [S]⟩
  have hK : orderedPosetClass (C.induce S) :=
    poset_weak_singleton_in_K C hTests x
  have hx : edge (C.induce S) .equiv sx sx := hK.2.1 sx
  have ht := (edge_embedding_iff (inclusion C S) .equiv sx sx).mpr hx
  exact ht

/-- Positive nontrivial partial-order comparisons are ALREADY
positive comparisons in the original weak strict vertex order.
There is no assumption that the whole weak source is a poset. -/
theorem poset_weak_equiv_implies_lt
    {V : Type} (C : RelStructure Lang V)
    (hTests : CorrectedUIrreduciblesIn
      orderedPosetClass (∅ : ClosureDescription Lang) C)
    (x y : V) (hne : x ≠ y)
    (hxy : edge C .equiv x y) :
    edge C .lt x y := by
  let S : Set V := {x, y}
  let sx : S := ⟨x, by simp [S]⟩
  let sy : S := ⟨y, by simp [S]⟩
  have hK : orderedPosetClass (C.induce S) :=
    poset_weak_binary_seed_in_K C hTests .equiv x y hxy
  have hsxy : edge (C.induce S) .equiv sx sy :=
    (edge_embedding_iff (inclusion C S) .equiv sx sy).mp hxy
  have hneS : sx ≠ sy := by
    intro heq
    exact hne (congrArg Subtype.val heq)
  have hlt : edge (C.induce S) .lt sx sy :=
    hK.2.2.2.2.1 sx sy hneS hsxy
  exact (edge_embedding_iff (inclusion C S) .lt sx sy).mpr hlt

/-- No positive auxiliary `.mate` tuple exists in a weak
candidate satisfying the corrected (4b) local test premise. -/
theorem poset_weak_no_mate
    {V : Type} (C : RelStructure Lang V)
    (hTests : CorrectedUIrreduciblesIn
      orderedPosetClass (∅ : ClosureDescription Lang) C)
    (x y : V) : ¬ edge C .mate x y := by
  intro hxy
  let S : Set V := {x, y}
  let sx : S := ⟨x, by simp [S]⟩
  let sy : S := ⟨y, by simp [S]⟩
  have hK : orderedPosetClass (C.induce S) :=
    poset_weak_binary_seed_in_K C hTests .mate x y hxy
  have hsxy : edge (C.induce S) .mate sx sy :=
    (edge_embedding_iff (inclusion C S) .mate sx sy).mp hxy
  exact hK.2.2.2.2.2 sx sy hsxy

/-- Positive diagonal order edges cannot occur even in a weak
candidate which is not a member of the ambient ordered class. -/
theorem poset_weak_lt_irrefl
    {V : Type} (C : RelStructure Lang V)
    (hTests : CorrectedUIrreduciblesIn
      orderedPosetClass (∅ : ClosureDescription Lang) C)
    (x : V) : ¬ edge C .lt x x := by
  intro hxx
  let S : Set V := {x}
  let sx : S := ⟨x, by simp [S]⟩
  have hK : orderedPosetClass (C.induce S) :=
    poset_weak_singleton_in_K C hTests x
  have hsxx : edge (C.induce S) .lt sx sx :=
    (edge_embedding_iff (inclusion C S) .lt sx sx).mp hxx
  exact hK.1.2.1 sx hsxx

end AllThoseRamseyClasses.Applications.OrderedPosets
