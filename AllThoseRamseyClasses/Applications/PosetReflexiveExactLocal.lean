import AllThoseRamseyClasses.Applications.PosetExactLocalCompletion
import Mathlib.Tactic

/-!
# Ordered-poset application: exact local obstruction with REFLEXIVE order

The 2019 manuscript uses reflexive binary orders, while the earlier
strict-walk theorem \`poset_no_quasiCycle_from_exact_weak_local_tests\`
requires *every* positive order edge (including loops) to strictly
increase the finite control. Its premise is therefore unsatisfiable
for a nonempty reflexive source.

Here only NONTRIVIAL original comparisons must increase the control.
A witness path is a walk of genuinely distinct successive vertices.
For such a path, a controlled finite order has at most |C0| vertices.
The exact induced weak-test completion then prevents introducing its
endpoint comparison on an already ordered source pair.

This establishes the valid reflexive-interface local obstruction,
NOT the full class instance or the existence of all such walks for
every edge in the reflexive-transitive closure.
-/

namespace AllThoseRamseyClasses.Applications

universe v w

/-- Reflexive source orders allow loops, so the strict-control
condition is imposed ONLY on distinct originally ordered pairs.
This is the actual hypothesis of the manuscript application. -/
theorem poset_reflexive_no_quasiCycle_from_exact_weak_local_tests
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
    (n : ℕ) (w : Fin (n + 1) → V)
    (hw : FiniteEdgeWalk (fun x y => p x y ∧ x ≠ y) n w)
    (hEndpoints : ord (w 0) (w (Fin.last n))) :
    p (w 0) (w (Fin.last n)) := by
  classical
  have hWalkD : ∀ i : Fin n,
      f (w i.castSucc) < f (w i.succ) := by
    intro i
    exact hOrd _ _ (hw i).2 (hP _ _ (hw i).1)
  have hbound : n + 1 ≤ Fintype.card D :=
    quasiCycle_control_card_bound (fun i => f (w i)) hWalkD
  let S : Finset V := Finset.univ.image w
  have hS : S.card ≤ Fintype.card D := by
    calc
      S.card ≤ Fintype.card (Fin (n + 1)) := by
        simpa [S] using (Finset.card_image_le (s := Finset.univ) (f := w))
      _ = n + 1 := Fintype.card_fin _
      _ ≤ Fintype.card D := hbound
  obtain ⟨q, hqRefl, hqTrans, hpq, hReflect⟩ := hLocal S hS
  have hIn : ∀ i, w i ∈ S := by
    intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hpqWalk : ∀ i : Fin n,
      q (w i.castSucc) (w i.succ) := by
    intro i
    exact hpq _ _ (hIn i.castSucc) (hIn i.succ) (hw i).1
  have hq : q (w 0) (w (Fin.last n)) :=
    finiteEdgeWalk_transitive_endpoints hqRefl hqTrans
      n w hw hpqWalk
  exact hReflect _ _ (hIn 0) (hIn (Fin.last n)) hEndpoints hq

end AllThoseRamseyClasses.Applications
