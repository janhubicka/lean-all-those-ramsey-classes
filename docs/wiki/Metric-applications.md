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

## The paper's finite block-convex orders

[PR #249](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/249)
closes the remaining **finite** convex-order interpretation.
The class `PaperBlockConvex S d` is defined literally by the
paper's block-equivalence relation: for every maximal no-jump
four-values block B, if the endpoints x≤z of an ordered
triple x≤y≤z satisfy `∃b∈B, d(x,z)≤b`, then
both (x,y) and (y,z) must satisfy the same B-relation.

    import AllThoseRamseyClasses.Applications.MetricBlockConvexity
    open AllThoseRamseyClasses.Applications.MetricSaturation
    #check paperBlockConvex_iff_jumpConvex
    #check paperBlockConvex_iff_capped_subset

The first theorem proves for a genuine finite-S metric that
the paper's block-convexity is **equivalent** to convexity
at all proper ambient jump thresholds. A non-top block has
a maximum jump by the certified finite decomposition in
PR #248. For a top block, all metric distances are at
most max S, so its equivalence relation is universal and
its convexity imposes no additional condition. Conversely,
each ambient jump j lies in its unique canonical block B_j
and is the maximum of B_j.

The second theorem is the exact finite-distance transfer:
if S is finite positive four-values and T is a finite
capped-closed subset of S, then any ordered metric with
distances in T is block-convex with respect to S exactly
when it is block-convex with respect to T. It combines
the checked jump-threshold transfer with the two
block/jump equivalences. The four-values property of T
is **derived** from cap closure, rather than assumed
as an extra premise.

The scalar finite-distance reduction and finite block-order
interface are consequently available as independent library
lemmas. This still does **not** construct the tagged lifted
metric, finish shortest-path completion on its closure
imaginaries, or prove the structural Ramsey arrow.

## One-point metric closure at a positive jump

[PR #250](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/250)
is the first **actual metric-construction** component for the paper's
closure vertices, rather than merely rounded-sum algebra or quotient labels.
It imports the previously verified genuine S-metric model
`MetricOn S d` and the neutral-zero operation on S∪{0}.

Given a positive jump j and a chosen original root r, define the
one-point extension on `Option V`, with `none` representing the new
closure vertex:

    d'(some x,some y) = d(x,y)
    d'(none,none) = 0
    d'(none,some x) = j ⊕ d(r,x)
    d'(some x,none) = d(x,r) ⊕ j.

The operation on the right is the *actual* rounded supremum with zero
neutral. `onePointDistance_metric` proves the extension is an S-metric:
all off-diagonal distances belong to S, symmetry and all triangle
cases hold, and original distances remain exactly unchanged.

The proof does not appeal to an unproved completion theorem. For
triangles with the new vertex as an endpoint, use the base metric
triangle, monotonicity and associativity of the zero-adjoined
rounded sum. For a triangle passing through the new vertex,
each edge dominates the corresponding original path segment.
All other triangles are already in the old metric.

    import AllThoseRamseyClasses.Applications.MetricOnePointClosure
    open AllThoseRamseyClasses.Applications.MetricSaturation
    #check onePointDistance_metric
    #check onePointDistance_to_class
    #check onePointDistance_new_class_iff
    #check onePointDistance_attachment_independent
    #check onePointDistance_maximal

The exact class theorem states that `d'(none,some x)≤j` if and only
if `d(r,x)≤j`; for any member of that class the distance to the
new vertex is *exactly* j. The attachment-independence theorem
states that attaching the new vertex to any other class member
with an edge of length j yields the same two-edge rounded
path length to every original vertex.

There is also a maximality theorem: any S-metric extension that
preserves old distances and has `d''(none,some r)=j` satisfies
`d''(none,some x)≤d'(none,some x)` for every x. This is the
maximal-distance property of the one-point shortest-path completion;
the separate walk-based completion API is not yet connected.

The full Lean build, source-integrity and permitted-axiom checks
passed in [CI 38761542466](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38761542466)
at source revision `876598f13aadca9282e18c52f389830cfc3d5c9c`.
`CheckAxiomsMetricOnePointClosure.lean` audits every new endpoint;
the module remains an active supported dependency in the inventory.

**Boundary:** this attaches *one* positive-jump closure vertex.
The paper's `L(A)` simultaneously attaches one quotient imaginary
per proper jump class, possibly at several levels. The distances
between those vertices, the tagged disjoint union, their order,
extension of embeddings and the full Ramsey-class proof still
need dedicated formalization. No theorem in this module certifies
`lem:Smetricemb` or the final Ramsey arrow.

## Two closure vertices and the inter-level metric formula

[PR #251](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/251)
iterates the checked one-point metric extension *twice*.
Original vertices are represented by `some (some x)`,
the first closure vertex by `some none`, and the second
by `none` in `Option (Option V)`.

Choose positive jumps j,k and original roots r,s. The resulting
distance is an actual S-metric (`twoPointDistance_metric`).
It leaves all original distances unchanged, and retains the
exact formulas

    d'(first,x) = j ⊕ d(r,x)
    d'(second,x) = k ⊕ d(s,x)
    d'(first,second) = j ⊕ d(r,s) ⊕ k.

All operations use the checked neutral-zero extension.
The first two formulas still give exact jump radius to every
original member of the corresponding jump class.
The third formula is proved **definitionally equal** to the
previously checked `quotientSandwichLabel` on the
j-class of r and the k-class of s. Associativity, metric
symmetry and commutativity show that swapping the attachment
order yields the same cross-distance.

    import AllThoseRamseyClasses.Applications.MetricTwoPointClosure
    open AllThoseRamseyClasses.Applications.MetricSaturation
    #check twoPointDistance_metric
    #check twoPointDistance_old
    #check twoPointDistance_closure_cross
    #check twoPointDistance_eq_quotientLabel
    #check twoPointDistance_cross_swap

Full Lean build, source integrity and permitted-axiom audit:
[CI 38763120354](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38763120354)
at code commit `02223d9a68690a7d44c7f6d6f39092d242aa56f5`.
The component is tested independently by
`CheckAxiomsMetricTwoPointClosure.lean`.

**Scope:** the two new vertices are distinct because they are
distinct tags in the nested Option carrier. If they represent
the same jump *and* the same block class, the paper's canonical
L(A) would identify them rather than attach two copies.
This theorem does not perform that deduplication, and does
not provide all levels, the extended order or embeddings.
Those tasks belong to the simultaneous tagged lift and
the still-open finite metric Ramsey proof.

## All pairwise distances in the finite closure tower

[PR #253](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/253)
strengthens #252 by identifying every formal closure vertex by its
attachment-stage index `i<n`:

    import AllThoseRamseyClasses.Applications.MetricClosureTowerLabels
    open AllThoseRamseyClasses.Applications.MetricSaturation
    #check towerClosure
    #check closureTowerDistance_closure_original
    #check closureTowerDistance_twoClosures

The `towerClosure` constructor transports the vertex from stage i
through all later Option layers. The first theorem proves its distance
to any original x at any later stage is still precisely

    levels(i) ⊕ d(roots(i), x).

For two *distinct* stages i,k<n, the second theorem proves

    d_tower(v_i,v_k)
        = levels(i) ⊕ d(roots(i),roots(k)) ⊕ levels(k).

The proof is induction on n. The old-old case reduces directly to
the previous stage's metric, the newest-to-original distances are
already checked, and the newest-to-old-closure case uses metric
symmetry and associativity of the actual zero-adjoined rounded sum.
The assumptions require proper jumps only at the stages i<n
actually used. The two-closure computation from #251 is a special
case; the formula for any two indices does not depend on attachments
made between them or on the attachment order.

The full Lean build, source-integrity and permitted-axiom audit passed
in [CI 38773004610](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38773004610)
at proof source commit `7ce3de99f39ce018fadea18763d4f4a14ebd460b`.
The dedicated audit is `CheckAxiomsMetricClosureTowerLabels.lean`.

**Canonical-lift boundary.** Stage indices still represent *formally
distinct* vertices, even if two stages use the same jump level and
the same original equivalence class. The next reusable interface
is an explicitly tagged carrier `V ⊕ Fin n` isometric to the tower;
thereafter choose one index per (jump,class) pair. An ordered
enumeration of the canonical classes, convex extension of the
vertex order, functorial embeddings, and full metric Ramsey
amalgamation/local-completion remain separate obligations.

## A directly tagged finite S-metric carrier

[PR #254](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/254)
reindexes the already verified closure tower on the user-facing
disjoint-union carrier `V ⊕ Fin n`:

    original x        = Sum.inl x
    closure stage i    = Sum.inr i

`taggedClosureDistance` is the actual checked tower distance
evaluated at the corresponding indexed vertices. Its explicit
metric entries are

    d'(inl x,inl y) = d(x,y)
    d'(inr i,inl x) = j_i ⊕ d(r_i,x)
    d'(inr i,inr k) = j_i ⊕ d(r_i,r_k) ⊕ j_k   (i≠k)
    d'(a,a)         = 0.

Crucially, `taggedClosureDistance_metric` verifies a **genuine**
S-metric on this disjoint union, not a pseudometric. The proof
does not assume the map to the underlying Option tower is
injective: for each type of distinct tagged vertices, it proves
the corresponding distance belongs to positive S using the
computed rounded formulas. Symmetry and triangles then follow
from the proved tower metric. Equal roots or equal jump levels
at different stages are allowed; their tags stay separate and
their distance remains positive.

    import AllThoseRamseyClasses.Applications.MetricTaggedClosure
    open AllThoseRamseyClasses.Applications.MetricSaturation
    #check taggedTowerVertex
    #check taggedClosureDistance
    #check taggedClosureDistance_old
    #check taggedClosureDistance_new_original
    #check taggedClosureDistance_new_new
    #check taggedClosureDistance_metric

The complete Lean build, source-integrity check and permitted-axiom
audit passed in
[CI 38774053990](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38774053990)
at source revision `dca9df110b5636b97d01a6018bf1fffeda8af104`.
The root `MetricTaggedClosure` is retained by the library's
active-module inventory.

**Canonical-lift boundary.** Stage indices need to be chosen to
enumerate each distinct (proper jump, original equivalence class)
exactly once. The metric on any such chosen enumeration is already
available, and the all-pair formulas imply it is independent of
representative choices. The existence of the canonical finite
tag enumeration, the concrete correspondence with the
paper's closure-vertex functions and order, and functorial
embedding extension remain to be formalized. No result here
certifies the complete L(A) lemma or finite Ramsey arrow.

## Canonical finite closure metric: exact class tags and explicit distances

[PR #255](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/255)
formalizes the **canonical** vertex type: a dependent pair of
a positive proper jump level j and one quotient class of the
original metric under `d(x,y)≤j`.
For finite S and finite original V the type
`CanonicalJumpTag` is finite and admits a bijection
`Fin n ≃ CanonicalJumpTag`, with **no duplicate tags**.
`canonicalTagRoot` chooses a representative in the class;
`canonicalTagRoot_class` proves it belongs to that quotient.
Full build and permitted-axiom audit:
[CI 38775275526](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38775275526).

[PR #257](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/257)
uses the bijection to transport the checked `V ⊕ Fin n` metric
onto **exactly** `V ⊕ CanonicalJumpTag`, with the correct
zero diagonal and all three explicit pairwise distance laws.
It certifies this is a *genuine* S-metric for a nonempty finite
base. A generic `metricOn_comap` isometry/pullback lemma
explicitly requires injectivity. Full Lean and source/axiom checks:
[CI 38778667880](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38778667880).
The superseded stacked PR #256 was closed because squash-merging #255
would have made its duplicate commits conflict; #257 is the clean
unstacked implementation.

[PR #258](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/258)
removes the arbitrary enumeration from the **public metric definition**:

    import AllThoseRamseyClasses.Applications.MetricCanonicalDistance
    open AllThoseRamseyClasses.Applications.MetricSaturation
    #check CanonicalJumpTag
    #check canonicalTagRoot_class
    #check canonicalDistance
    #check canonicalDistance_new_old
    #check canonicalDistance_new_new
    #check canonicalDistance_metric

`canonicalDistance` is defined directly on the duplicate-free
carrier `V ⊕ CanonicalJumpTag`. It is d on original vertices,
equals `j ⊕ d(root,x)` on closure/original pairs, and is
`j ⊕ d(root,root') ⊕ k` for **distinct** closure tags;
the diagonal is zero. The chosen class representatives are
internal to the definition, not additional user arguments.
The existing quotient-sandwich theorem establishes the
mathematical representative-independence of these labels.

`canonicalDistance_metric` checks the explicit function by
identifying its distances with the metric whose existence
was proved in #257. It also handles **empty V** separately:
then no quotient class tags exist and all metric axioms are
vacuous. No default or fictitious original root is introduced.
Full project build, source-integrity and permitted-axiom audit:
[CI 38779692029](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38779692029).

**Remaining boundary:** the metric on canonical vertices is now
constructed. The paper also requires a specific convex extension
of the given linear order, functions pointing from original
vertices to each closure representative, and extension of
embeddings to the lifted structures. Strong amalgamation,
exact weak local completion and the finite Ramsey arrow
remain distinct class-level obligations. The current theorem
does **not** certify the complete `lem:Smetricemb`.

## Isometric transport of jump-equivalence classes

[PR #260](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/260)
formalizes the canonical class map induced by an **exact
isometry** of original S-metric spaces. For each proper
jump level j (and for zero), d(x,y)≤j holds precisely when
d(f(x),f(y))≤j, since the embedding preserves all distances.

    import AllThoseRamseyClasses.Applications.MetricCanonicalQuotientMap
    open AllThoseRamseyClasses.Applications.MetricSaturation
    #check mapJumpClass
    #check mapJumpClass_mk
    #check mapJumpClass_injective
    #check mapCanonicalJumpTag
    #check mapCanonicalJumpTag_level
    #check mapCanonicalJumpTag_class_mk

`mapJumpClass` is constructed by a genuine `Quotient.liftOn`;
its computation on representatives is explicit, and
`mapJumpClass_injective` uses **reflection**, not merely
preservation, of the threshold relation. The dependent
`mapCanonicalJumpTag` preserves the positive jump level
and sends a class represented by x to the corresponding
class represented by f(x). These are reusable library
components even when the underlying vertex sets are
infinite, and require no finite distance-set assumption.

The full Lean build, source-integrity and permitted-axiom
checks passed in [CI 38781956316](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38781956316)
at proof source commit `d5460f18c3e38cbcebaf57521616be27d42db85f`.

The full canonical metric embedding has **not** yet been
proved: it additionally needs injectivity on the dependent
canonical tag family and comparison of every mixed and
cross metric label. Preserving the prescribed convex
linear order remains a separate obligation.

## Representative-independent canonical metric labels

[PR #261](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/261)
makes representative independence a **directly importable**
property of the explicit canonical metric. The clean
main-based implementation supersedes a conflicted but
previously passing PR #259.

    import AllThoseRamseyClasses.Applications.MetricCanonicalLabelInvariance
    open AllThoseRamseyClasses.Applications.MetricSaturation
    #check canonicalDistance_mixed_quotientLabel
    #check canonicalDistance_cross_quotientLabel
    #check canonicalDistance_mixed_anyRoot
    #check canonicalDistance_cross_anyRoots

For every closure tag (j,E) and original vertex x, the
mixed distance equals the two-variable quotient sandwich
label with the singleton zero-level class of x. For two
distinct closure tags (j,E),(k,F), their distance equals
the sandwich label of E and F. Hence either chosen root
may be replaced by **any original representative of the
same threshold class** without changing the result.
Equality of canonical tags, not equality of chosen
representatives, determines the zero diagonal.

The full Lean build, source-integrity and permitted-axiom
audit passed in
[CI 38798821065](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38798821065)
at source revision `99e496f2bf8239c4e632bceb7547d89fe61d08ed`.
PR #261 merged as
`c6f94dce957a747e20f9719a151ac6d2c2a5490a`.

[PR #274](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/274)
combines this result with the quotient transport from #260.
Its theorem `mapCanonicalLift_isometry` checks every old/old,
mixed and distinct closure/closure metric distance under the
induced map on canonical tags; `mapCanonicalLift_injective`
derives injectivity from positive off-diagonal S-distances.
Full CI [38812329333](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38812329333)
passed, and PR #274 merged as
`92104fea0a546974a15e51d005d05b77ed813b00`.
The order-preserving part of the embedding is still separate.

## Complete nested closure-function assignments

[PR #273](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/273)
formalizes the partial closure function F_j on **every** lifted
vertex, including the previously omitted nested-level cases:

    F_j(old x)             = (j,[x]_j)
    F_j(new (k,E)), k<j    = (j,[root(E)]_j)
    F_j(new (k,E)), k>=j   = undefined.

It proves the first two formulas are compatible with the
original class quotient and independent of which root
represents E. The new F_j edge from a lower-jump closure
vertex has **metric length exactly j**. This closes the
specific function-table gap in the S={1,3,9} regression,
not yet the entire ordered-functional class axiom.
Complete CI [38813295544](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38813295544)
passed; the PR merged as
`b152fec45e13759efc374736abe5263994e21edd`.

## Canonical finite insertion order

[PR #270](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/270)
defines a genuine linear order on the canonical tagged
carrier by the faithful lexicographic keys

    old x       -> (x, bottom)
    tag (j,E)   -> (lastOriginal(E), j).

The checkable `canonicalClassLast` comes from the proved
finite class-max theorem in PR #266. The insertion key
is injective because the pair (jump level, last original
member) determines E uniquely. The order restricts to
the original vertex order, puts each new closure vertex
strictly after its last original class member, and
places smaller-jump closure vertices first when
nested tags share an anchor. This avoids the
S={1,3,9} order inversion regression.
Full integration CI [38824390934](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38824390934)
passed; the PR merged as
`566219d68cfdfa414ce60cf65afb8270212cfa48`.

The **stronger** theorem that the closure representative
is last among *all* vertices of its completed jump
equivalence class, rather than merely last original
anchor, is being checked in
[PR #279](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/279).
Convexity of all completed jump classes and preservation
of this order under lifted embeddings remain separate
proof obligations.

## 20 October: ordered empty base and finite-base shortest-path interfaces

**Completed and full-CI verified:** [PR #516](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/516)
(merge `5ec658e0`, `MetricEmptyBaseOrderedAmalgamation.lean`).
The verified separated metric on the disjoint sum U ⊕ V can be equipped
with a *genuine* linear sum order, old U vertices first and old V
vertices second, retaining each side order exactly. At every proper
jump j of S, the cross distance is `max S > j`, so a j-class is
contained wholly in one side. Convexity of the two original orders
therefore gives `separatedSumDistance_jumpConvex`. For finite
positive four-values S the checked equivalence between threshold
convexity and literal maximal-no-jump **paper block convexity**
gives `separatedSumDistance_paperBlockConvex`, including empty
summands. The former `MetricEmptyBaseAmalgamation` already verifies
all ordinary metric triangles and S-valuedness of this separated
distance. This now closes the **ordered metric** empty-base branch,
not the completed F_j partial-function amalgamation.

**Complete Lean build, axiom audit and admission scan passed** for
the following independently importable nonempty-base components,
now all merged on `main`:

| Verified PR | Exported result and scope |
| --- | --- |
| [#518](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/518) | A finite nonempty base has an attained minimum `min_a(p(a) ⊕ q(a))`; the old abstract j-crossing theorem's minimum/attainment premises follow automatically |
| [#519](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/519) | Cross-minimum symmetry, actual S-membership, strictly positive off-side distances and bounds by a common maximum |
| [#521](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/521) | For genuine S-metric endpoints outside the embedded finite root, cross distance ≤ j iff some base point is within j of both endpoints |
| [#522](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/522) | Scalar real triangle `x ⊕ c ≤ a + (b ⊕ c)` for S-valued x,a,b,c with x≤a+b, derived from the real-supremum rounded operation |
| [#524](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/524) | Actual one-cross mixed triangle `δ(x,z) ≤ d_U(x,y)+δ(y,z)` for two off-base LEFT endpoints |
| [#526](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/526) | Mirrored one-cross mixed triangle `δ(x,z) ≤ δ(x,y)+d_V(y,z)` for two off-base RIGHT endpoints |

The exact rounded distance chosen by a nonempty-base finite
shortest path is now well-defined, attained, strictly positive,
symmetric and has the required proper-jump crossing criterion.
Both one-cross mixed triangles are certified; all of these
statements use actual S-valued metrics and **ordinary real**
triangle inequalities, not a guessed associative abstract monoid.

**All finite-root metric triangles are now verified.** The
scalar/two-cross work in [#533](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/533),
[#535](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/535),
[#537](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/537)
and the cross/base cases
[#538](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/538)/
[#543](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/543)
all passed full Lean CI and merged. The complete actual
identified-root carrier is in [#541](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/541);
the exact distance table has a zero diagonal, symmetry and positive
S-values by [#542](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/542).
The remaining real metric triangles, in all 27 possible location
patterns, are assembled into a genuine `MetricOn S` theorem in
[#547](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/547)
(full CI [39414556962](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/39414556962)).
Both original sides embed **isometrically** by
[#545](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/545);
their images overlap **only on the prescribed root** by
[#548](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/548).
This closes the **finite nonempty-base METRIC strong amalgamation**,
with exact old metrics and no accidental identifications.

**The order and functions remain separate.**
[#553](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/553)
(full CI [39473087370](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/39473087370))
constructs an ordinary common linear order extending both original
orders. That alone is **not jump-convex**: take S={1,3}, root {r},
left ordered r<x<v with d(r,x)=1 and d(r,v)=d(x,v)=3,
and right ordered r<y with d(r,y)=1. The private-priority order
r<x<v<y separates the j=1 class {r,x,y} by v.

The precise class geometry is stronger. The checked
[#557](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/557)
(full CI [39474380725](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/39474380725))
proves that any two original vertices on opposite sides are
j-close at a proper jump exactly when a COMMON root vertex is
j-close to both, including endpoints that already lie in the
root. PR [#560](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/560)
separately constructs the exact union of the two side j-classes
above each root class; as of this note it remains under CI.
The proof plan
[for recursively amalgamating the finite nested jump classes](../metric-rooted-convex-order-proof-20261020.md)
was merged in [#558](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/558).
It is a **standalone English proof plan**, not a Lean validation of
the compatible convex order. It explicitly replaces the invalid
idea of ordering all private vertices by one global root-cut key.

## 27 October: full functional strong-amalgamation components

The full **finite nonempty-root ordered-functional strong
amalgamation** has now been proved in
[PR #645](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/645)
(complete main build and allowed-axiom audit
[40401430039](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/40401430039)).
Exported theorem:
`MetricSaturation.metricRooted_finiteS_functionalStrongAmalgam_exists`
in `MetricFiniteFunctionalStrongAmalgam.lean`.

It constructs the ACTUAL identified-base finite S-metric,
its full paper-block-convex order, all Option-valued
partial functions F_j, every genuine proper-jump
designated-last/undefined closure law, induced restrictions
(including undefinedness) to BOTH original sides, and
exact strong overlap. The source hypotheses require two
valid functional structures, a **nonempty** common base
embedded isometrically and in order, and exact root
function-value equality:
`fU(j,iU(a))=Option.map(iU)(fA(j,a))`, and likewise on V.
This is a closed-root strong-amalgamation theorem, not
a proof that arbitrary weak substructures have completions.

**Empty common root, nonempty S.**
The disjoint sum distance at `max S` preserves the
paper's convex order (#349/#516). PR
[#647](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/647)
(full CI 40399508890) verifies the COMPLETE
`MetricJumpClosureLaw` for each F_j in the disjoint-sum
functional language, preserving both original partial
functions. The one-theorem packaging is PR
[#652](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/652);
treat it as pending until full CI succeeds.

**S empty.**
[PR #648](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/648)
(CI 40400708995) proves that an S-metric on the empty
allowed positive distance set has at most one vertex:
a strong amalgam of two distinct singleton copies
over the empty root is impossible. This does not
challenge the trivial Ramsey property of the class.
The corresponding local correction to the printed
auxiliary strong-amalgamation statement is proposed
in manuscript author-review PR #145.

## Remaining metric Ramsey work

The major unfinished application obligation is the
**exact original weak local-completion property**
in the printed `lem:finite4value2`, including its
quantification over weak induced subsets, the uniform
cutoff `2|S|(|J_S|+1)`, and proof that an
unimportant short path in the incomplete candidate has
one common F_j closure. None of these follow merely from
strong amalgamation of already valid, closed structures.

The preceding cycle-compression lemma
`lem:Sequivalence` contains a concrete endpoint issue.
With S={1,3}, the four-values property holds and the
triangle with edge lengths (1,1,3) is nonmetric,
but its three vertices exceed the printed bound |S|=2.
The proposed smallest upper-bound repair is
`max(3,|S|)`; the rest of the cycle/path-replacement
argument and its effect on the numerical local
cutoff still need independent proof. The candidate
manuscript correction is PR #164 and the focused Lean
regression is #650, under audit.

A new local-completion line of work is
[PR #653](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/653),
which checks closure-representative coherence on a j-short
edge, and its reflection through an injective local
completion preserving exact partial function values.
It does not yet prove whole-path closure propagation or
the exact weak-subset cutoff.

Finite canonical lifted metric/embeddings and the
finite capped distance-extension theorem (#244/#342)
remain verified. But the full finite S-metric Ramsey
arrow and finite-to-infinite S transfer in
`prop:Smetric` remain unverified. Infinite-S maximal
blocks require a separate exact source-definition
audit, and mathematical prose repairs #132/#135/#136/#139/
#145/#164 are author-review PRs, not silently merged.

Consult the [manuscript proof-difference ledger](https://github.com/janhubicka/All-those-Ramsey-classes/blob/main/APPLICATIONS-PRINTED-PROOF-DIFFERENCES-2026-10-20.md)
for the precise distinction between verified statements,
alternative proofs, still-open printed steps and proposed
localized corrections.
