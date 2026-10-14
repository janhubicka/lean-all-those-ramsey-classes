import AllThoseRamseyClasses.Applications.PosetReflexiveExactLocal
import AllThoseRamseyClasses.Applications.PosetTransitiveClosure
import Mathlib.Data.List.Chain
import Mathlib.Data.Fintype.Card

/-!
# All quasi-cycle paths, not just an explicitly supplied finite walk

The existing reflexive exact-weak-test theorem in
`PosetReflexiveExactLocal` handles a path GIVEN as a finite Fin-indexed
walk. To use it for the actual application, an arbitrary comparison
in `Relation.TransGen` must produce an exact weak finite set of
bounded size. This module establishes the stronger endpoint directly
from a genuine finite path extracted by the list-chain theorem.

No global injectivity of the control map is assumed. Strict increase
on distinct original order edges makes the list of CONTROL labels
strictly increasing; that alone bounds its length by `|C0|`.
We test the *original vertex list's toFinset* (not its closure) and
use transitivity in the local completion to reflect its endpoints.

The resulting theorem is exactly the missing endpoint-exclusion
bridge needed before proving the poset's complete local-completion
class instance. Strong amalgamation and that final class bridge
remain separate.
-/

namespace AllThoseRamseyClasses.Applications

universe v w

/-- A finite strictly controlled list path has at most as many
vertices as control values, and in particular its exact vertex
support passes the original local cutoff. -/
theorem poset_isChain_support_card_bound
    {V : Type v} {D : Type w}
    [LinearOrder D] [Fintype D]
    (p : V → V → Prop) (f : V → D)
    (hStrict : ∀ x y : V, p x y → f x < f y)
    (l : List V) (hl : List.IsChain p l) :
    l.toFinset.card ≤ Fintype.card D := by
  classical
  have hStrictChain : List.IsChain (· < ·) (l.map f) :=
    List.IsChain.isChain_map_of_isChain f
      (fun a b hab => hStrict a b hab) hl
  have hPairwise : List.Pairwise (· < ·) (l.map f) :=
    List.isChain_iff_pairwise.mp hStrictChain
  have hNodup : (l.map f).Nodup := hPairwise.nodup
  calc
    l.toFinset.card ≤ l.length := List.toFinset_card_le l
    _ = (l.map f).length := by simp
    _ ≤ Fintype.card D := hNodup.length_le_card

/-- Arbitrary transitive paths obey endpoint reflection when the
original **exact** weak subsets of at most |C0| vertices have
protected K-completions. Unlike the earlier path lemma, this
conclusion does not assume the path is supplied as data. -/
theorem poset_reflexive_no_quasiCycle_of_transGen
    {V : Type v} {D : Type w}
    [Fintype V] [LinearOrder D] [Fintype D]
    (ord p : V → V → Prop) (f : V → D)
    (hOrd : ∀ x y : V, x ≠ y → ord x y → f x < f y)
    (hP : ∀ x y : V, p x y → ord x y)
    (hLocal :
      ∀ S : Finset V, S.card ≤ Fintype.card D →
        ∃ q : V → V → Prop,
          (∀ a : V, q a a) ∧
          (∀ a b c : V, q a b → q b c → q a c) ∧
          (∀ x y, x ∈ S → y ∈ S → p x y → q x y) ∧
          (∀ x y, x ∈ S → y ∈ S →
            ord x y → q x y → p x y))
    {x y : V}
    (hReach : Relation.TransGen (posetStrictPart p) x y)
    (hOrdXY : ord x y) :
    p x y := by
  classical
  obtain ⟨l, hl, hEnd⟩ :=
    List.exists_isChain_cons_of_relationReflTransGen
      hReach.to_reflTransGen
  let S : Finset V := (x :: l).toFinset
  have hStrict : ∀ a b : V, posetStrictPart p a b →
      f a < f b := by
    intro a b hab
    exact hOrd a b hab.2 (hP a b hab.1)
  have hBound : S.card ≤ Fintype.card D :=
    poset_isChain_support_card_bound (posetStrictPart p)
      f hStrict (x :: l) hl
  obtain ⟨q, hqRefl, hqTrans, hpq, hReflect⟩ :=
    hLocal S hBound
  have hChainQ : List.IsChain q (x :: l) := by
    apply hl.imp_of_mem_imp
    intro a b ha hb hab
    exact hpq a b
      (List.mem_toFinset.mpr ha)
      (List.mem_toFinset.mpr hb)
      hab.1
  have hAll : ∀ z ∈ x :: l, q x z := by
    apply List.IsChain.induction (fun z => q x z) (x :: l)
      hChainQ
    · intro a b hab hxa
      exact hqTrans x a b hxa hab
    · intro _
      exact hqRefl x
  have hEndQ : q x y := by
    have hLastQ :
        q x ((x :: l).getLast (List.cons_ne_nil x l)) :=
      hAll _ (List.getLast_mem _)
    rwa [hEnd] at hLastQ
  exact hReflect x y
    (List.mem_toFinset.mpr (List.mem_cons_self))
    (by
      have hMemLast : (x :: l).getLast (List.cons_ne_nil x l) ∈ x :: l :=
        List.getLast_mem _
      rw [hEnd] at hMemLast
      exact List.mem_toFinset.mpr hMemLast)
    hOrdXY hEndQ

/-- Full reflection for the reflexive/transitive closure, including
the diagonal. The diagonal case is reflected by the singleton
local test rather than silently presuming p has all loops. -/
theorem poset_reflexive_weak_local_reflects_reach
    {V : Type v} {D : Type w}
    [Fintype V] [LinearOrder D] [Fintype D]
    (ord p : V → V → Prop) (f : V → D)
    (hOrd : ∀ x y : V, x ≠ y → ord x y → f x < f y)
    (hP : ∀ x y : V, p x y → ord x y)
    (hReflexive : ∀ x : V, p x x)
    (hLocal :
      ∀ S : Finset V, S.card ≤ Fintype.card D →
        ∃ q : V → V → Prop,
          (∀ a : V, q a a) ∧
          (∀ a b c : V, q a b → q b c → q a c) ∧
          (∀ x y, x ∈ S → y ∈ S → p x y → q x y) ∧
          (∀ x y, x ∈ S → y ∈ S →
            ord x y → q x y → p x y)) :
    ∀ x y : V,
      ord x y → posetReachClosure (posetStrictPart p) x y →
      p x y := by
  intro x y hxy hReach
  rcases hReach with hEq | hPath
  · subst y
    exact hReflexive x
  · exact poset_reflexive_no_quasiCycle_of_transGen
      ord p f hOrd hP hLocal hPath hxy

end AllThoseRamseyClasses.Applications
