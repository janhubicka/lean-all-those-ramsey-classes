import AllThoseRamseyClasses.Applications.PosetWeakLocalLaws
import AllThoseRamseyClasses.Applications.PosetExactWeakCompletion

/-!
# Exact weak K-completions give the relation-valued local poset tests

The source-faithful corrected 2019 clause (4c) gives, for each exact
small vertex set S, a K-target and a positive map on C|S which is
FULL on every induced closed U-irreducible test. In the ordered-poset
case U is empty: all tests are closed, but not every weak S is itself
irreducible or injectively embedded.

The finite-control path argument needs a *relation q on the whole
weak carrier* which is reflexive/transitive, extends p on S, and
REFLECTS p on every originally ordered pair from S. Construct q
as the pullback of the target partial order on S plus the diagonal
outside S. This does not assume a global embedding of C|S.

The key reflection case is a positive original strict-order pair:
its exact two-vertex support is ordinarily irreducible, so the
corrected completion map is FULL on that support, and its E-relation
is reflected. The diagonal uses the independently verified actual
singleton K-membership (4b), not any fictitious global ordering.
-/

namespace AllThoseRamseyClasses.Applications.OrderedPosets

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published
open AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

private theorem binary_support_irreducible
    {X : Type} (A : RelStructure Lang X)
    (R : Symbol) (x y : X) (hRel : edge A R x y) :
    (A.induce ({x,y} : Set X)).Irreducible := by
  let T : Set X := {x,y}
  let sx : T := ⟨x, by simp [T]⟩
  let sy : T := ⟨y, by simp [T]⟩
  have hTuple : edge (A.induce T) R sx sy :=
    (edge_embedding_iff (inclusion A T) R sx sy).mp hRel
  have hPoint : ∀ t : T, t = sx ∨ t = sy := by
    intro t
    have ht : t.1 = x ∨ t.1 = y := by
      have h : t.1 ∈ ({x,y} : Set X) := t.2
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
    rcases ht with ht | ht
    · exact Or.inl (Subtype.ext ht)
    · exact Or.inr (Subtype.ext ht)
  intro a b hne
  rcases hPoint a with ha | ha <;> rcases hPoint b with hb | hb
  · exact (hne (ha.trans hb.symm)).elim
  · subst a
    subst b
    exact ⟨R, ![sx,sy], 0, 1, hTuple, rfl, rfl⟩
  · subst a
    subst b
    exact ⟨R, ![sx,sy], 1, 0, hTuple, rfl, rfl⟩
  · exact (hne (ha.trans hb.symm)).elim

/-- A genuine original weak K-completion yields the four exact
relation-valued axioms needed by the finite-control path argument:
reflexive/transitive q, preservation of p on S and reflection on
every originally ordered pair in S. Nothing is assumed about the
vertices outside S except the diagonal. -/
theorem poset_weak_completion_produces_local_relation
    {V : Type} (C : RelStructure Lang V)
    (S : Finset V)
    (hReflexive : ∀ x : V, edge C .equiv x x)
    (hComplete : HasInducedClosedUKCompletion
      orderedPosetClass (∅ : ClosureDescription Lang)
      (C.induce (↑S : Set V))) :
    ∃ q : V → V → Prop,
      (∀ a : V, q a a) ∧
      (∀ a b c : V, q a b → q b c → q a c) ∧
      (∀ x y, x ∈ S → y ∈ S →
        edge C .equiv x y → q x y) ∧
      (∀ x y, x ∈ S → y ∈ S →
        (x = y ∨ edge C .lt x y) → q x y →
        edge C .equiv x y) := by
  classical
  let P : Set V := ↑S
  let A : RelStructure Lang P := C.induce P
  obtain ⟨W, hW, Target, hKTarget, _, f, hf⟩ := hComplete
  let q : V → V → Prop :=
    fun a b => a = b ∨
      ∃ (ha : a ∈ P) (hb : b ∈ P),
        edge Target .equiv (f ⟨a, ha⟩) (f ⟨b, hb⟩)
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · intro a
    exact Or.inl rfl
  · intro a b c hab hbc
    rcases hab with hab | ⟨ha, hb, hab⟩
    · subst b
      exact hbc
    rcases hbc with hbc | ⟨hb', hc, hbc⟩
    · subst c
      exact Or.inr ⟨ha, hb, hab⟩
    · right
      refine ⟨ha, hc, ?_⟩
      have heq : (⟨b, hb⟩ : P) = ⟨b, hb'⟩ :=
        Subtype.ext rfl
      rw [← heq] at hbc
      exact hKTarget.2.2.1 _ _ _ hab hbc
  · intro x y hx hy hxy
    right
    refine ⟨hx, hy, ?_⟩
    let sx : P := ⟨x, hx⟩
    let sy : P := ⟨y, hy⟩
    have hSrc : edge A .equiv sx sy :=
      (edge_embedding_iff (inclusion C P) .equiv sx sy).mp hxy
    have hTarget := hf.1 .equiv ![sx,sy] hSrc
    have ht : f ∘ ![sx,sy] = ![f sx, f sy] := by
      funext i
      fin_cases i <;> rfl
    change Target.rel .equiv (f ∘ ![sx,sy]) at hTarget
    rw [ht] at hTarget
    exact hTarget
  · intro x y hx hy hOrd hq
    rcases hOrd with hxy | hlt
    · subst y
      exact hReflexive x
    rcases hq with hxy | ⟨hx', hy', hTarget⟩
    · subst y
      exact hReflexive x
    let sx : P := ⟨x, hx⟩
    let sy : P := ⟨y, hy⟩
    have hOldLt : edge A .lt sx sy :=
      (edge_embedding_iff (inclusion C P) .lt sx sy).mp hlt
    let Pair : Set P := {sx,sy}
    have hIrr : (A.induce Pair).Irreducible :=
      binary_support_irreducible A .lt sx sy hOldLt
    have hClosed : IsUClosed
        (∅ : ClosureDescription Lang) (A.induce Pair) := by
      intro rule hrule
      simp at hrule
    obtain ⟨e, he⟩ := hf.2 Pair hClosed
      (hIrr.isUIrreducible (∅ : ClosureDescription Lang))
    let xx : Pair := ⟨sx, by simp [Pair]⟩
    let yy : Pair := ⟨sy, by simp [Pair]⟩
    have hxEq : (⟨x, hx'⟩ : P) = sx := Subtype.ext rfl
    have hyEq : (⟨y, hy'⟩ : P) = sy := Subtype.ext rfl
    rw [hxEq, hyEq] at hTarget
    have hEtarget : edge Target .equiv (e xx) (e yy) := by
      rw [he xx, he yy]
      exact hTarget
    have hPairE : edge (A.induce Pair) .equiv xx yy :=
      (edge_embedding_iff e .equiv xx yy).mp hEtarget
    have hAE : edge A .equiv sx sy :=
      (edge_embedding_iff (inclusion A Pair) .equiv xx yy).mpr hPairE
    exact (edge_embedding_iff (inclusion C P) .equiv sx sy).mpr hAE

end AllThoseRamseyClasses.Applications.OrderedPosets
