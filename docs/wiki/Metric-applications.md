# Metric applications: exact proof boundaries

The scalar finite-distance reduction is formalized in the modules below.
The full S-metric Ramsey applications are not yet certified. In particular,
`prop:Smetric` is a Ramsey proposition, not merely a finite-generation lemma.
See [Applications](Applications.md) for completed Ramsey-class examples.

## Finite four-values extensions

```lean
import AllThoseRamseyClasses.Applications.MetricFourValues
open AllThoseRamseyClasses.Applications.MetricSaturation
#check associativeOn_iff_fourValues
#check exists_finite_fourValues_extension
#check exists_finite_capped_extension
#check distanceSum_subset_eq_capped
```

`distanceSum S a b` is the actual real supremum

    sup {s in S : s <= a + b}.

`WellDefined S` says that this supremum belongs to S for operands in S.
`Positive S` says every allowed distance is positive. `FourValues S` is
exactly the manuscript's pair-of-triangles condition: whenever a,b,x and
c,d,x satisfy the triangle inequalities for some x in S, there is y in S
such that a,c,y and b,d,y satisfy the triangle inequalities. All four side
orderings and triangle equalities are allowed.

**Finite reduction.** If S is positive, its rounded sum is well-defined,
and S satisfies four-values, then every finite D contained in S lies in
a finite T contained in S whose own rounded sum is well-defined and which
also satisfies four-values. This is `exists_finite_fourValues_extension`.
Neither topological closedness nor a finite number of blocks is assumed.
If D is empty, T may be empty; no cap or positive generator is chosen.

[PR #244](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/244)
contains the source, full-build review and permitted-axiom checks in
`CheckAxiomsMetricFiniteGeneration.lean`. The active inventory retains the
metric dependency chain without disabling cleanup or integrity checks.
These are directly importable components; they are not exported as an
unfinished Ramsey class by `ApplicationsAPI`.

## Proof architecture

### One generator reaches a maximum

This part was checked in
[PR #243](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/243).
For a,m in S with 0<a<=m, set x(0)=a and
x(n+1)=min(m, x(n) ⊕_S a). The terms belong to S and are at most m.
Let l be their supremum and choose n with l-a<x(n). Every x(k) is an
allowed candidate below x(n)+a and below m, hence x(k)<=x(n+1).
Thus x(n+1) is a maximum; nondecreasing powers give a constant tail.
The proof does not assume l belongs to S. It uses neither associativity
nor commutativity. Its endpoints are `exists_power_max`,
`exists_power_stable`, `power_eq_of_stable`, and `finite_range_power`.

### Several generators: finite joins, without exponent bookkeeping

The reusable module `AllThoseRamseyClasses.FiniteSemigroup` proves:

```lean
#check AllThoseRamseyClasses.FiniteSemigroup.finite_sup
#check AllThoseRamseyClasses.FiniteSemigroup.finite_closure_singleton
#check AllThoseRamseyClasses.FiniteSemigroup.finite_closure
```

In a commutative semigroup, the join of finite subsemigroups A and B is
contained in the finite subsemigroup A ∪ B ∪ AB. A singleton-generated
subsemigroup lies in its positive-power range. Induction on the finite
set of generators now proves finiteness of the actual Mathlib
`Subsemigroup.closure`. No identity, cancellation, empty product, or
finite ambient carrier is assumed. This is a shorter formal route than
encoding bounded exponent vectors. No numerical normal-form bound is
claimed as a separately formalized theorem.

For distances, use the subtype of allowed values at most m, with product
`cappedSum S m a b = min m (distanceSum S a b)`. Its associative law is
proved from the original rounded sum, not assumed independently.
`MetricFiniteGeneration` identifies generic positive powers with the
already checked distance powers and applies the finite-closure theorem.

### The restricted operation is the correct one

For a cap-closed T contained in S below m, and a,b in T,

    distanceSum T a b = min(m, distanceSum S a b).

Every candidate in T is below the right side. Conversely the right side
belongs to T by cap-closure and is at most a+b, so it is itself a candidate.
This proves `distanceSum_subset_eq_capped`. Well-definedness and
associativity of T's own rounded sum follow. This identity needs no
finiteness or topological closedness of T.

### Four-values and associativity, in both directions

`associativeOn_iff_fourValues` is proved for positive S with well-defined
rounded sum. For associativity implying four-values, choose the missing
diagonal to be the smaller of a⊕c and b⊕d; monotonicity, associativity and
the existing triangles give the remaining inequalities. Conversely,
apply four-values to the triangles a,b,a⊕b and (a⊕b)⊕c,c,a⊕b.
The new diagonal t satisfies t<=b⊕c and (a⊕b)⊕c<=a+t. This gives one
associativity inequality; reversing a and c gives the other.
Thus the final finite extension starts from the original four-values
hypothesis and returns four-values, rather than assuming an unproved bridge.

## Idempotent jump sandwich

`Applications.MetricJumpSandwich` independently proves
`MetricJump.sandwich_constant_on_parts`. The algebraic proof permits
idempotent zero thresholds and does not use commutativity. Its specialization
to S-distance jumps still requires the neutral-zero convention and the
precise block-equivalence/triangle-inequality bridge.

## Remaining metric Ramsey work

The scalar reduction does not construct a Ramsey witness or a class-level
completion. Remaining tasks are the finite metric Ramsey theorem,
closure-vertex representation, compatible convex orders, strong amalgamation,
exact weak local-completion bounds, and the finite-to-arbitrary-distance
Ramsey transfer. In particular, convex-order compatibility when passing
between S and the finite extension T is a separate obligation, not a
consequence already asserted by the scalar extension theorem.

The old scalar finite-generation TODO in the manuscript's review material
is superseded by the new component certificate once PR #244 passes the full
CI gates. The full `prop:Smetric` and `thm:Smetric` remain partial.
