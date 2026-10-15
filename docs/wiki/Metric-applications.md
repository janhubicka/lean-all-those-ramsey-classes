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

## Convexity at jump thresholds: finite reduction

[PR #245](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/245)
adds two reusable modules:

- MetricJumpThresholds identifies the manuscript jump criterion
  (j is nonmaximal and no S-distance lies in (j,2j]) with a proper
  rounded-sum idempotent. It shows all proper jumps of a cap-closed
  subset T are ambient jumps, and that an ambient jump j<m is either
  invisible to T or has the same distance threshold as the largest
  t in T below j, itself a T-jump.
- MetricConvexityTransfer formalizes interval convexity of the relation
  d(x,y)<=j on a linearly ordered vertex set. When distinct vertices
  have T-distances and d(x,x)=0, it proves that this property at all
  S-jumps is equivalent to the same property at all T-jumps.

Import and inspect these endpoints:

    import AllThoseRamseyClasses.Applications.MetricConvexityTransfer
    open AllThoseRamseyClasses.Applications.MetricSaturation
    #check jump_iff_gap
    #check exists_restricted_jump_below
    #check jumpConvex_iff_of_capped_closed
    #check exists_finite_fourValues_jumpConvex_extension

The last theorem combines this transport with finite four-values
generation: for any finite D of distances in S used by an ordered
structure, it returns a finite T containing D, with well-defined
four-values operation and an exact equivalence between jump-threshold
convexity for S and T. This also handles D empty: the vertex set
must then have at most one element.

**Scope caution.** This is not yet the full paper's block-convex
metric Ramsey theorem. For finite four-values distance sets, jumps
index the proper block equivalences, but the identification of
block-convexity with this threshold formulation (especially for
infinite S), the closure-vertex representation and the finite metric
Ramsey theorem are separate formal obligations. The jump algebra
does not itself construct Ramsey witnesses.

The proofs use the actual real-supremum operation. No ambient finite
block count, topological closedness, metric symmetry or triangle
inequality is added to the order-theoretic transfer. The real metric
conditions will enter when relating thresholds to block equivalences.
The new endpoints have a separate permitted-axiom audit in
CheckAxiomsMetricConvexityTransfer.lean.

## Corrected metric jump sandwich and the zero convention

[PR #246](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/246)
specializes the previously checked abstract
`MetricJump.sandwich_constant_on_parts` to **actual S-metrics**,
including both zero-radius cases. It introduces
`Applications.MetricZeroExtension` and
`Applications.MetricJumpSamedist`.

`WithZero S` is the actual ordered subtype S∪{0}; `sumWithZero`
returns the original real-supremum rounded sum on positive operands,
and has neutral zero on the diagonal. `zeroOp` is a closed operation on
that subtype. Its associativity and both monotonicity laws are proved
from the corresponding properties of the rounded S-operation, rather
than assumed. Each positive jump j is an idempotent because
`distanceSum S j j=j`; zero is an idempotent by the neutral convention.

`MetricOn S d` has exactly the metric hypotheses: zero diagonal,
S-valued distances off the diagonal, symmetry and the ordinary triangle
inequality. `metric_triangle_rounded` derives the stronger triangle
inequality for `sumWithZero` (including zero). The reusable
`metric_sandwich_constant_on_parts` now gives the required invariance
of the sandwiched cross-distance.

    import AllThoseRamseyClasses.Applications.MetricJumpSamedist
    open AllThoseRamseyClasses.Applications.MetricSaturation
    #check metric_triangle_rounded
    #check metric_samedist_threshold_classes
    #check blockClass_eq_thresholdClass
    #check metric_samedist_bounded_blocks
    #check metric_samedist_bounded_blocks_distinct

The last theorem is the paper's corrected block-class argument under
the explicit facts `j∈B` and `∀b∈B, b≤j`, together with either
`j=0` or `Jump S j`. The class represented by a root is then exactly
the set of vertices at distance at most j from the root. The sandwich
expression is constant on the two classes; if the roots are distinct
(as for disjoint classes), the constant lies in S. This algebraic
statement does not require S to be finite and does not require the
two classes to be disjoint just for constancy.

**Exact remaining interface.** The manuscript asserts that for finite
four-values S every non-top block has a maximum j which is a jump, and
uses the trivial zero equivalence for j=0. The formal proof explicitly
takes the maximum-of-block facts as hypotheses; the formalization of the
paper's maximal-no-jump block decomposition is not yet included.
Accordingly the original lemma receives a scoped partial marker until
that representation fact is checked. The printed four-point proof is
not valid at j=0; the nonprinting TeX addendum records the neutral-zero
replacement rather than rewriting the frozen numbered proof.

## Quotient-invariant cross-labels for closure imaginaries

[PR #247](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/247)
takes the next step toward the lifted metric structure.

The new `Applications.MetricJumpQuotient` proves that
`d(x,y)≤j` defines a genuine `Setoid` for each allowed level
`j=0` or a positive proper jump of S: reflexivity comes from the
zero diagonal, symmetry from the metric, and transitivity from
jump idempotency. Its `JumpClasses` type is the ordinary quotient
by this relation.

`quotientSandwichLabel` descends the expression
`j1⊕d(u,v)⊕j2` to a pair of quotient classes, by invoking
the already proved zero-radius sandwich lemma for alternative
representatives. This label is independent of both representatives,
and it is S-valued for distinct representatives. No finiteness
assumption on S or the metric's vertex set is used.

    import AllThoseRamseyClasses.Applications.MetricJumpQuotient
    open AllThoseRamseyClasses.Applications.MetricSaturation
    #check jumpSetoid
    #check quotientSandwichLabel
    #check quotientSandwichLabel_mk
    #check quotientSandwichLabel_mem_of_distinct

**Important distinction:** this cross-label is not itself a metric
on a quotient. If a closure imaginary is compared with itself,
the diagonal must be assigned zero rather than the sandwich
value (which may be positive). The eventual tagged vertex set,
inter-level closure representatives, shortest-path completion,
strong amalgamation and convex order are additional obligations.
Thus `lem:Smetricemb` and the finite metric Ramsey class remain
only partially validated.

## Verified canonical finite blocks and the corrected manuscript lemma

[PR #248](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/248)
formalizes the paper's **literal block definition**, rather than
presupposing a decomposition: a `PaperBlock S B` is an
inclusion-maximal subset B of S satisfying the four-values
condition and containing no jump in the elementary gap sense.

For finite positive four-values S, `wellDefined_of_finite`
first proves the real-supremum rounded operation is automatically
well-defined. Define the **jump-cut signature** of a distance a
by the truth values of `a ≤ j` for all proper S-jumps j.
The piece `JumpPiece S a` contains exactly the members of S with
the same signature as a. Its properties are proved in stages:

1. Each piece is finite and has a greatest member m. It is closed
   under the original ambient rounded sum capped at m. It therefore
   has its own well-defined associative rounded operation and is
   four-values; no arbitrary-subset inheritance is assumed.
2. An internal jump of a piece would also be an ambient jump, which
   contradicts the equal signature of two members straddling it.
3. Every *arbitrary finite no-jump subset* of S stays on one side
   of every ambient jump cut. Otherwise the greatest member t below
   a cut j would itself be an internal jump: every larger member
   is above j and therefore above 2j ≥ 2t.
4. Maximality identifies exactly these canonical pieces with
   the paper's maximal no-jump four-values blocks.
5. Every non-top block has a maximum which is an ambient jump.
   Furthermore, any block containing a particular ambient jump j
   has maximum exactly j, and the block containing j is unique.

    import AllThoseRamseyClasses.Applications.MetricPaperBlockSamedist
    open AllThoseRamseyClasses.Applications.MetricSaturation
    #check wellDefined_of_finite
    #check jumpPiece_fourValues
    #check jumpPiece_noGapJumps
    #check jumpPiece_isPaperBlock
    #check paperBlock_eq_jumpPiece
    #check paperBlock_proper_max_isJump
    #check paperBlock_unique_at_jump

### The corrected finite-S Lemma samedist

`PaperGapBlockAtLevel` now expresses exactly either the trivial
zero block {0}, or a positive level j satisfying the paper's
gap-jump definition, together with the (now certified) paper
block containing j. The theorem

    #check finite_paperBlock_samedist_published

starts with finite positive S, four-values and a genuine S-metric.
It takes two such levels and disjoint rooted block-equivalence
classes, and produces a constant belonging to S for the expression
j1⊕d(u,v)⊕j2, independent of u,v. All zero-radius cases are
included and the block maxima and well-defined rounded sums
are *derived*, not assumptions.

This proves the **mathematical corrected lemma** with the explicit
neutral convention `0⊕a=a⊕0=a`. The numbered published text
does not declare that convention before using j=0, and its
four-point proof cannot construct zero-length edges. The TeX
circulation body remains frozen. Its validation addendum records
the repaired statement and distinguishes it from the literal
printed notation. The full metric lift and Ramsey arrow are
separate obligations.

### Adversarial regression

Adding the next larger distance one at a time does not preserve
four-values. S={2,3,4,5,7} and B={2,3,5} both have four-values,
and B has no internal jump, but B∪{7} fails four-values:
triangles (2,3,5) and (2,7,5) require replacement diagonal 4
for side pairs (2,2) and (3,7). The missing distance 4 is essential.
The formal proof therefore uses full jump-signature pieces,
not single-distance extensions. This small finite regression is
a mathematical audit, not a separately claimed Lean computation.

## Remaining metric Ramsey work

The scalar reduction does not construct a Ramsey witness or a class-level
completion. Remaining tasks are the finite metric Ramsey theorem,
closure-vertex representation, the full block-equivalence interpretation
of jump thresholds (especially for infinite S), strong amalgamation,
exact weak local-completion bounds, and the finite-to-arbitrary-distance
Ramsey transfer. Jump-threshold convexity itself is now transported, but
its identification with the paper's full block-convexity is not automatic.

The old scalar finite-generation TODO in the manuscript's review material
is superseded by the new component certificate once PR #244 passes the full
CI gates. The full `prop:Smetric` and `thm:Smetric` remain partial.
