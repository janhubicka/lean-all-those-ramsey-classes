import AllThoseRamseyClasses.Applications.PosetMetricBounds
import Mathlib.Tactic

/-!
# Exact weak local poset tests prevent quasi-cycles

This works with the paper's actual situation: the weak source has a
not-yet-transitive order relation, mapping strictly into the fixed
finite linear-order control. The target of the small-test completion
is a reflexive and transitive relation q on an arbitrary finite
subset; it must preserve every original poset edge and REFLECT
the poset relation on old ordered pairs. It is not enough to have
a completion in the ambient arbitrary-ordered class.

For any finite poset-edge walk the control is strictly increasing,
so its number of vertices is <= |C0|. The local condition on the
exact induced vertex subset containing the walk then forces its
endpoint comparison to have been an original poset edge. This is
a genuine quantifier-level reduction of arbitrary quasi-cycle
obstructions to n(C0)=|C0| weak tests.

The remaining step of the full poset application is packaging the
finite-walk characterization of the transitive closure, compatible
linear-order extension, strong amalgamation and the corrected 2019
class hypothesis. No full Ramsey theorem is asserted here.
-/

namespace AllThoseRamseyClasses.Applications

universe v w

/-- A length-n directed walk, given by its n+1 successive vertices. -/
def FiniteEdgeWalk {V : Type v} (p : V → V → Prop)
    (n : ℕ) (w : Fin (n + 1) → V) : Prop :=
  ∀ i : Fin n, p (w i.castSucc) (w i.succ)

/-- If a reflexive transitive relation contains every edge of a
finite directed walk, then it contains the endpoint comparison. -/
theorem finiteEdgeWalk_transitive_endpoints
    {V : Type v} {p q : V → V → Prop}
    (hqRefl : Reflexive q) (hqTrans : Transitive q)
    (n : ℕ) (w : Fin (n + 1) → V)
    (hw : FiniteEdgeWalk p n w)
    (hpq : ∀ i : Fin n, q (w i.castSucc) (w i.succ)) :
    q (w 0) (w (Fin.last n)) := by
  induction n with
  | zero =>
      exact hqRefl (w 0)
  | succ n ih =>
      let w' : Fin (n + 1) → V := fun i => w i.castSucc
      have hw' : FiniteEdgeWalk p n w' := by
        intro i
        exact hw i.castSucc
      have hpq' : ∀ i : Fin n, q (w' i.castSucc) (w' i.succ) := by
        intro i
        exact hpq i.castSucc
      have hfirst : q (w 0) (w (Fin.castSucc (Fin.last n))) := by
        simpa only [w'] using ih w' hw' hpq'
      have hlast : q (w (Fin.castSucc (Fin.last n)))
          (w (Fin.last (n + 1))) := by
        exact hpq (Fin.last n)
      exact hqTrans hfirst hlast

/-- The finite-control bound on exact weak local completions detects
ALL finite quasi-cycle walks, not merely the first n steps of a walk.

The local target relation q may depend on S. The assumption hReflect
is exactly protection of an original ORDER-related irreducible pair:
a completion must not introduce a poset edge between that pair unless
it was already present in the source. -/
theorem poset_no_quasiCycle_from_exact_weak_local_tests
    {V : Type v} {D : Type w}
    [Fintype V] [LinearOrder D] [Fintype D]
    (ord p : V → V → Prop) (f : V → D)
    (hOrd : ∀ x y, ord x y → f x < f y)
    (hP : ∀ x y, p x y → ord x y)
    (hLocal :
      ∀ S : Finset V, S.card ≤ Fintype.card D →
        ∃ q : V → V → Prop,
          Reflexive q ∧ Transitive q ∧
          (∀ x y, x ∈ S → y ∈ S → p x y → q x y) ∧
          (∀ x y, x ∈ S → y ∈ S →
            ord x y → q x y → p x y))
    (n : ℕ) (w : Fin (n + 1) → V)
    (hw : FiniteEdgeWalk p n w)
    (hEndpoints : ord (w 0) (w (Fin.last n))) :
    p (w 0) (w (Fin.last n)) := by
  classical
  have hWalkD : ∀ i : Fin n,
      f (w i.castSucc) < f (w i.succ) := by
    intro i
    exact hOrd _ _ (hP _ _ (hw i))
  have hbound : n + 1 ≤ Fintype.card D :=
    quasiCycle_control_card_bound (fun i => f (w i)) hWalkD
  let S : Finset V := Finset.univ.image w
  have hS : S.card ≤ Fintype.card D := by
    calc
      S.card ≤ Fintype.card (Fin (n + 1)) := by
        simpa [S] using Finset.card_image_le Finset.univ w
      _ = n + 1 := Fintype.card_fin _
      _ ≤ Fintype.card D := hbound
  obtain ⟨q, hqRefl, hqTrans, hpq, hReflect⟩ := hLocal S hS
  have hIn : ∀ i, w i ∈ S := by
    intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hpqWalk : ∀ i : Fin n,
      q (w i.castSucc) (w i.succ) := by
    intro i
    exact hpq _ _ (hIn i.castSucc) (hIn i.succ) (hw i)
  have hq : q (w 0) (w (Fin.last n)) :=
    finiteEdgeWalk_transitive_endpoints hqRefl hqTrans
      n w hw hpqWalk
  exact hReflect _ _ (hIn 0) (hIn (Fin.last n)) hEndpoints hq

end AllThoseRamseyClasses.Applications
