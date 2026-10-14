import Mathlib.Order.RelClasses
import Mathlib.Tactic

/-!
# Correcting the metric jump-distance invariance argument

This is the algebraic core of the 2019 application's Lemma
`lem:samedist`. The printed four-vertex construction assumes that
zero jump parameters are positive metric distances, so it cannot
handle the explicitly permitted j₁=0 or j₂=0.

Instead, for any monotone associative distance semigroup, sandwiching
a distance between two idempotent thresholds is invariant under
perturbations of size at most those thresholds. This uses *only*
two triangle inequalities and idempotency; neither a four-point
amalgam nor an unrelated extra metric assumption is needed.

For an S-metric distance set, every jump j satisfies j⊕j=j; the
zero case uses the neutral extension on S ∪ {0}. The separate
specialization checking the paper's S-metric definitions is still
an application obligation. This module is a self-contained, reusable
algebraic proof and does NOT certify that specialization.
-/

namespace AllThoseRamseyClasses.Applications.MetricJump

universe u v

/-- Idempotent threshold sandwiching absorbs one extra copy of
each threshold, without assuming commutativity. -/
theorem sandwich_absorb
    {D : Type u} (op : D → D → D)
    (hAssoc : ∀ a b c : D, op (op a b) c = op a (op b c))
    (p q x : D) (hp : op p p = p) (hq : op q q = q) :
    op (op p (op (op p x) q)) q = op (op p x) q := by
  calc
    op (op p (op (op p x) q)) q =
        op p (op (op p x) (op q q)) := by
          rw [hAssoc p (op (op p x) q) q, hAssoc (op p x) q q]
    _ = op p (op (op p x) q) := by rw [hq]
    _ = op (op p p) (op x q) := by
          rw [hAssoc p x q, ← hAssoc p p (op x q)]
    _ = op p (op x q) := by rw [hp]
    _ = op (op p x) q := (hAssoc p x q).symm

/-- One-sided estimate for the corrected jump lemma.
Only two small within-class perturbations are used. -/
theorem sandwich_le
    {D : Type u} [Preorder D] {V : Type v}
    (op : D → D → D)
    (hAssoc : ∀ a b c : D, op (op a b) c = op a (op b c))
    (hMonoL : ∀ {a b c : D}, a ≤ b → op a c ≤ op b c)
    (hMonoR : ∀ {a b c : D}, a ≤ b → op c a ≤ op c b)
    (d : V → V → D)
    (hTriangle : ∀ a b c : V, d a c ≤ op (d a b) (d b c))
    (p q : D) (hp : op p p = p) (hq : op q q = q)
    (u u' v v' : V)
    (hU : d u' u ≤ p) (hV : d v v' ≤ q) :
    op (op p (d u' v')) q ≤ op (op p (d u v)) q := by
  have hdist :
      d u' v' ≤ op (op (d u' u) (d u v)) (d v v') := by
    calc
      d u' v' ≤ op (d u' u) (d u v') :=
        hTriangle u' u v'
      _ ≤ op (d u' u) (op (d u v) (d v v')) :=
        hMonoR (hTriangle u v v')
      _ = op (op (d u' u) (d u v)) (d v v') :=
        (hAssoc _ _ _).symm
  have hbound : d u' v' ≤ op (op p (d u v)) q := by
    calc
      d u' v' ≤ op (op (d u' u) (d u v)) (d v v') := hdist
      _ ≤ op (op p (d u v)) (d v v') :=
        hMonoL (hMonoL hU)
      _ ≤ op (op p (d u v)) q :=
        hMonoR hV
  calc
    op (op p (d u' v')) q ≤
        op (op p (op (op p (d u v)) q)) q :=
      hMonoL (hMonoR hbound)
    _ = op (op p (d u v)) q :=
      sandwich_absorb op hAssoc p q (d u v) hp hq

/-- Corrected equal-distance lemma. Both thresholds can be
idempotent zero; no nonzero lower bound is assumed. -/
theorem sandwich_eq
    {D : Type u} [PartialOrder D] {V : Type v}
    (op : D → D → D)
    (hAssoc : ∀ a b c : D, op (op a b) c = op a (op b c))
    (hMonoL : ∀ {a b c : D}, a ≤ b → op a c ≤ op b c)
    (hMonoR : ∀ {a b c : D}, a ≤ b → op c a ≤ op c b)
    (d : V → V → D)
    (hTriangle : ∀ a b c : V, d a c ≤ op (d a b) (d b c))
    (p q : D) (hp : op p p = p) (hq : op q q = q)
    (u u' v v' : V)
    (hu : d u' u ≤ p) (hu' : d u u' ≤ p)
    (hv : d v v' ≤ q) (hv' : d v' v ≤ q) :
    op (op p (d u v)) q = op (op p (d u' v')) q := by
  apply le_antisymm
  · exact sandwich_le op hAssoc hMonoL hMonoR d hTriangle
      p q hp hq u' u v' v hu' hv'
  · exact sandwich_le op hAssoc hMonoL hMonoR d hTriangle
      p q hp hq u u' v v' hu hv

/-- Invariant across two classes with uniformly small within-class
distances. Handles singleton (zero-radius) classes as well. -/
theorem sandwich_constant_on_parts
    {D : Type u} [PartialOrder D] {V : Type v}
    (op : D → D → D)
    (hAssoc : ∀ a b c : D, op (op a b) c = op a (op b c))
    (hMonoL : ∀ {a b c : D}, a ≤ b → op a c ≤ op b c)
    (hMonoR : ∀ {a b c : D}, a ≤ b → op c a ≤ op c b)
    (d : V → V → D)
    (hTriangle : ∀ a b c : V, d a c ≤ op (d a b) (d b c))
    (p q : D) (hp : op p p = p) (hq : op q q = q)
    (part1 part2 : Set V)
    (hPart1 : ∀ x ∈ part1, ∀ y ∈ part1, d x y ≤ p)
    (hPart2 : ∀ x ∈ part2, ∀ y ∈ part2, d x y ≤ q)
    (u u' v v' : V) (hu : u ∈ part1) (hu' : u' ∈ part1)
    (hv : v ∈ part2) (hv' : v' ∈ part2) :
    op (op p (d u v)) q = op (op p (d u' v')) q := by
  exact sandwich_eq op hAssoc hMonoL hMonoR d hTriangle
    p q hp hq u u' v v'
    (hPart1 u' hu' u hu) (hPart1 u hu u' hu')
    (hPart2 v hv v' hv') (hPart2 v' hv' v hv)

end AllThoseRamseyClasses.Applications.MetricJump
