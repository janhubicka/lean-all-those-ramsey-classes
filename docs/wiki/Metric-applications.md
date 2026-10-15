# Metric applications: exact proof boundaries

The full S-metric Ramsey applications are not yet certified. This page
separates the numerical and algebraic components from the remaining
class-level constructions. See [Applications](Applications.md) for completed
Ramsey-class examples.

## Rounded sums and positive powers

Import the component directly, without importing a not-yet-proved Ramsey
application into `ApplicationsAPI`:

```lean
import AllThoseRamseyClasses.Applications.MetricSaturation
open AllThoseRamseyClasses.Applications.MetricSaturation
#check exists_power_max
#check exists_power_stable
#check power_eq_of_stable
#check finite_range_power
```

`distanceSum S a b` is the actual real supremum

    sup {s in S : s <= a + b}.

`WellDefined S` says that this supremum belongs to S whenever both operands
belong to S. This is not an assumption that powers stabilize.
`cappedSum S m a b` is the minimum of m and this supremum.
The hypotheses for stabilization are exactly:

* `WellDefined S`;
* `m ∈ S` and `a ∈ S`;
* `0 < a` and `a ≤ m`.

There is no assumption that S is finite, topologically closed, or has
finitely many blocks. Associativity and commutativity are unnecessary
for this one-generator result. In particular, the proof applies to
infinite nonclosed allowed-distance sets whenever the rounded sum is
well-defined.

### The maximum argument

Write x(0)=a and x(n+1)=min(m, x(n) ⊕_S a). All terms belong to S and
are at most m. Let l be the supremum of their range. Since a>0, some
x(n) satisfies l-a<x(n). For every k,

    x(k) <= l < x(n) + a,
    x(k) <= m.

Thus x(k) is an allowed candidate in the supremum defining the next
rounded sum, and x(k)<=x(n+1). Consequently x(n+1) is a maximum of
the whole sequence. Nondecreasing powers then give two equal successive
terms; the recursion makes the entire tail constant.

**No circular closedness assumption:** l is not assumed to belong to S.
Attainment by a power is proved using `le_cappedSum` and the bounded
range. No strict-increase contradiction or convergence theorem is needed.

**Index convention:** Lean's `power ... 0` is the first positive power,
not an identity element. If `exists_power_stable` returns N, the exponent
at stabilization is N+1. `power_eq_of_stable` handles every later term,
and `finite_range_power` gives the finite range directly.

Proof and CI review: [PR #243](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/243).
Every endpoint is covered by `CheckAxiomsMetricSaturation.lean` and the full
project build. The active-module inventory explicitly retains this
application component; the cleanup check is not bypassed.

## From one generator to finitely many: next formal obligation

For finitely many positive generators, associativity and commutativity
allow grouping each nonempty word by generator. Replace the exponent
of each generator by the smaller of that exponent and its positive
stabilization exponent. This gives finitely many normal forms.

With Lean stabilization indices N_i, the number of possible nonempty
normal forms is at most the product of (N_i+2), minus one: the exponent
of generator i ranges from 0 through N_i+1. Zero here means omission
of a generator, not a zero distance. An empty generator set and a metric
space with no positive distances must be handled separately.

This normal-form argument, the proof that the capped operation restricts
to the rounded operation on the generated finite set, and the four-values
transfer are **not** certified by `finite_range_power`. They are the next
steps toward manuscript `prop:Smetric`.

## Idempotent jump sandwich

`Applications.MetricJumpSandwich` independently proves
`MetricJump.sandwich_constant_on_parts`. The algebraic proof permits
idempotent zero thresholds and does not use commutativity. Its specialization
to S-distance jumps still requires the neutral-zero convention and the
precise block-equivalence/triangle-inequality bridge.

## What remains outside these certificates

The metric closure-vertex representation, convex orders, strong amalgamation,
exact weak local-completion bounds, and the final finite and infinite
S-metric Ramsey transfers remain separate obligations. No complete green
marker on `prop:Smetric` or `thm:Smetric` follows from either component.
