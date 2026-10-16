# Public API reference (validated 2019 theorem)

This document is written for mathematicians and Lean users citing or
applying Hubička–Nešetřil, *All those Ramsey classes* (2019). It
documents **exactly which definitions to use** for the corrected
relational theorem, the names of the checked statements, and the
additional hypotheses needed to specialize the theorem.

**Core import:**

Use `AllThoseRamseyClasses.ApplicationsAPI` (or the curated root
`AllThoseRamseyClasses`) for the verified ordered-poset, paper graph,
acyclic digraph, K_n-free graph, positive-tournament-free oriented
digraph families, pointed-equivalence, finite-target
m-unary, and auxiliary Steiner Ramsey theorems.
The core `PublicAPI` stays independent of individual applications.
See the [research wiki's applications reference](wiki/Applications.md).

**Preferred import:**

```lean
import AllThoseRamseyClasses.PublicAPI

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published
```

The single import above is itself checked in
[`CheckAxiomsPublicAPI.lean`](../CheckAxiomsPublicAPI.lean).
The example
[`Examples/MainTheorem.lean`](../AllThoseRamseyClasses/Examples/MainTheorem.lean)
is built by CI.

## Namespaces and source layers

| Namespace | Source layer | Purpose |
| --- | --- | --- |
| `StructuralRamsey` | pinned `partite-construction` | `RelLanguage`, `RelStructure`, `Arrow`, finite Ramsey/colouring foundations |
| `StructuralRamsey.RelStructure` | pinned `partite-construction` | `Embedding`, class predicates, closure-description operations, free amalgamation, protected maps |
| `AllThoseRamseyClasses.Published` | this repository | exact printed-versus-corrected definitions, coordinated corrected main result and audited 2019 lemmas |
| `StructuralRamsey.Structure` | pinned `partite-construction` | finite structures with primitive partial/set-valued functions, including a checked genuinely single-valued theorem |
| `AllThoseRamseyClasses.Applications.*` | this repository | application **components** and specialized named languages; not every class-level Ramsey corollary is complete |

The pinned revision is specified by the top-level
[`lakefile.toml`](../lakefile.toml), not by the newest upstream
commit. Working directly on the proof dependency can otherwise
change declarations and proof assumptions.

## Ramsey and embedding foundations

```lean
#check StructuralRamsey.RelLanguage
#check StructuralRamsey.RelStructure
#check StructuralRamsey.RelStructure.Embedding
#check StructuralRamsey.RelStructure.Irreducible
#check StructuralRamsey.RelStructure.IsHomomorphismEmbedding
#check StructuralRamsey.Arrow
#check StructuralRamsey.RelStructure.FiniteRamseyClass
```

A relational language has a type of relation symbols and a finite
natural-number arity for each symbol. A structure interprets those
symbols on functions `Fin n → V`. The semantics do not silently
exclude repetitions or arity zero. The `Embedding` API always
includes **injectivity and reflection** of every positive and
negative relation tuple:

```lean
e.map_rel_iff R tuple
```

Thus a mere positive homomorphism is insufficient when an
application needs an induced copy. Ordinary `Irreducible` means
complete Gaifman graph, whereas `IsHomomorphismEmbedding`
requires a full embedding on each ordinarily irreducible
induced substructure. The arrow definition is:

```text
Arrow A B C κ
  = for every colouring of Embedding A C by κ,
    some Embedding B C makes all Embedding A B subcopies
    of that B-copy monochromatic.
```

`FiniteRamseyClass K` quantifies over **all** finite members
`A,B ∈ K` and every nonempty finite colour type `κ : Type`.
It requires a finite `C ∈ K`, not merely a completion outside
the class. All theorems below use full embeddings for copies.

## Closure descriptions: Definition 2.12 onward

```lean
#check ClosureRule
#check ClosureDescription
#check IsUClosed
#check IsUSemiClosed
#check IsUSubstructure
#check UClosureHull
#check USize
#check IsUIrreducible
```

A `ClosureRule L` has fields:

| Field | Meaning |
| --- | --- |
| `symbol : L.Symbol` | The relation whose tuples implement this rule |
| `rootSize : ℕ` | Number of initial root coordinates |
| `rootPositive : 0 < rootSize` | Original 2019 roots are **nonempty** |
| `rootStrict : rootSize < L.arity symbol` | Some nonroot/output position exists |
| `root : RelStructure L (Fin rootSize)` | A **full irreducible structure** serving as the root |
| `rootIrreducible : root.Irreducible` | Explicit irreducibility certificate |

A `ClosureDescription L` is a set of rules; it can contain
multiple rules and need not have a finite symbol type.

`rule.IsClosed A` requires (1) every positive closure tuple's
initial coordinates to realize a **full copy** of the specified
root, and (2) **exactly one entire output tuple** for each such
root embedding. Outputs can overlap root coordinates. In
`IsUSemiClosed` the output is optional but still unique when
present.

An `IsUSubstructure rules A S` uses the literal subset
`S : Set V`. If a positive closure tuple has every root
coordinate in `S`, its *every* coordinate is in `S`.
This condition never replaces `S` with an automatically
generated hull. The latter is a separate operation,
`UClosureHull rules A S`.

For `A` actually `U`-closed, the checked Lemma 2.23(1)
is:

```lean
#check AllThoseRamseyClasses.Published.lemma_2_23_one
```

It states that the structure induced on `S` is intrinsically
closed **iff** `S` is a relative U-substructure of `A`.
The free amalgam is closed when the two sides **and the
common root** are closed (Lemma 2.23(2),
`IsFreeAmalgam.isUClosed`). The root condition cannot be
deleted: separate closure outputs from the two sides could
then conflict.

The number `USize rules A` is the minimum number of vertices
generating `A`. It need not equal `|A|` and need not equal
the cardinality of the closure of a particular weak subset.
In particular `n(B,C0)` in the local axiom counts the
**original tested vertices**, not generators and not closure
hull size.

## Which irreducibility is involved?

There are **three different** conditions:

1. `A.Irreducible`: any two distinct vertices share a positive
   tuple (ordinary relational Gaifman irreducibility).
2. `IsUIrreducible rules A`: `A` has no free decomposition
   into two proper *intrinsically U-closed* sides. This can hold
   even when `A` itself is not U-closed.
3. `IsUClosed rules A ∧ IsUIrreducible rules A`: the
   **protected tests** of the coordinated repaired theorem.

Do not replace the third by the second, or infer the third
from the first without also proving closedness.

## Literal-versus-corrected maps and exact weak completions

**Published Definition 2.15 (comparison of predicates):**

```lean
#check IsUHomomorphismEmbedding
```

This predicate protects **every** intrinsically U-irreducible
induced test, even nonclosed ones. The theorem certified in this
library instead uses the paired changes to Definition 2.15 and
Definition 2.17(4b), requiring U-closedness together with
U-irreducibility. This comparison specifies which theorem is
formalized; it does not offer an editorial verdict on the
original published formulation.

**Corrected paper-style map:**

```lean
#check IsInducedClosedUHomomorphismEmbedding
#check HasInducedClosedUKCompletion
#check InducedClosedULocalCompletionAt
```

The map is a positive relational homomorphism
`f : V → W`. For **each exact original induced set**
`S : Set V`, if `A.induce S` is both `IsUClosed`
and `IsUIrreducible`, the restriction of `f`
must equal a full `Embedding (A.induce S) Target`.
The map itself need not be globally injective.
A corrected `K`-completion has an actual finite
irreducible `K`-member as target and such a map from
the original source.

There is also an abstract-carrier working representation

```lean
#check IsClosedUHomomorphismEmbedding
#check HasClosedUKCompletion
#check ClosedULocalCompletionAt
```

from the dependency. It quantifies over full **embedded**
closed/irreducible test objects rather than only the chosen
subtype `A.induce S`. The checked direction
`IsClosedUHomomorphismEmbedding.toInducedClosed`
and `InducedClosedULocalCompletionAt.toAbstractClosed`
is legitimate. For a raw, arbitrary class predicate, the
two presentations are **not automatically equivalent**
without appropriate isomorphism closure. Use the
explicit bridge theorems, never definitional rewriting.

## Class hypotheses of the corrected 2019 theorem

```lean
#check InducedClosed2019Hereditary
#check InducedClosed2019MultiamalgamationClass
#check IsomorphismClosed2019
#check IsCoordinated2019MultiamalgamationClass
```

The corrected paper-style
`InducedClosed2019MultiamalgamationClass R K rules`
has fields:

| Field | Obligation |
| --- | --- |
| `subset` | Every `K`-member is in the ambient `R` |
| `finite` | All `K`-members have finite carriers |
| `closed` | All `K`-members are intrinsically `U`-closed |
| `hereditary` | Every **induced U-closed** substructure of a `K`-member is in `K` |
| `strong` | Two `K`-members have a finite strong amalgam over a common **K-member**, with no extra vertex identification |
| `localCompletion` | For every finite `B ∈ K`, finite `C0 ∈ R`, choose a fixed $n(B,C_0)$ satisfying the corrected exact weak-test implication |

`IsCoordinated2019MultiamalgamationClass` packages
these six properties with an additional `iso` field:
`IsomorphismClosed2019 K`. A polymorphic
`StructureClass` does **not** come with this property.
The ambient class `R` being Ramsey and ordinarily
irreducible is supplied separately to the main theorem.

### Local axiom: quantifiers and implication direction

To show
`InducedClosedULocalCompletionAt K rules B C0 n`,
fix an arbitrary finite **candidate C**. Assume:

1. `IsUClosed rules C`.
2. `C0.Irreducible` and there is a corrected protected
   homomorphism-embedding `C → C0`. The original `C0`
   itself need not be U-closed.
3. **Each original exact induced** test of `C` that is both
   intrinsically U-closed and U-irreducible lies in `K`.
4. For **each original exact weak**
   `S : Finset C` with `S.card ≤ n`, the **original
   `C.induce S`** has a corrected K-completion.
   This includes nonclosed tests and the empty subset.

Then conclude `HasCopywiseCompletion K B C`. This
is a map into a finite K-target that preserves **all
full B-copy embeddings** in `C`. No global embedding
of the whole weak source is demanded.

This class condition is an implication. Weakening its
antecedent makes the **condition stronger**, not weaker.
The coordinated repair weakens the protected-map tests
and the (4b) membership tests together; one must not
reverse this logical direction.

## Theorems and completion infrastructure

**Stable unrestricted researcher entry points:**

```lean
#check coordinated2019_theorem218
#check coordinated2019_ramsey_by_profile_sparsening
#check coordinated2019_profile_sparse_witness
#check lemma_2_28_coordinated_unrestricted_induced
```

* `coordinated2019_ramsey_by_profile_sparsening` proves
  `FiniteRamseyClass K` from `FiniteRamseyClass R`,
  ordinary irreducibility of all `R`-members, and
  `IsCoordinated2019MultiamalgamationClass R K rules`.
  It constructs the missing sparse witness itself.
* `coordinated2019_theorem218` is the exact same
  fully proved assertion packaged in the existing
  universal proposition
  `Coordinated2019Theorem218Target`. This is especially
  convenient when consuming the theorem from another file.
* `coordinated2019_profile_sparse_witness` constructs
  the closed Ramsey candidate at **every specified cutoff n**
  from a Ramsey arrow with no closedness assumption on
  the original control `C0`. Its requirements include
  K-closedness, K strong amalgamation, closed heredity and
  K ordinary irreducibility; it does **not** assume a
  sparse-witness or rank-step constructor.
* `lemma_2_28_coordinated_unrestricted_induced`
  constructs a closed initial Ramsey Picture over the
  originally selected (possibly nonclosed) control.

**Construction and transport theorems:**

| Declaration | Role |
| --- | --- |
| `coordinated2019_to_abstract_closed_class` | Prove the one-way exact-induced to embedded-test class bridge, with isomorphism invariance. |
| `IsCoordinated2019MultiamalgamationClass.toAbstract` | Apply the same bridge directly to the packaged class. |
| `closedHereditary2019_iff_embedded` | Relate paper-style induced heredity and abstract embedded heredity **under isomorphism invariance**. |
| `closureProfileExpansion2019` | Expand structures with records of genuinely closed generating hulls in the base. |
| `closureProfile2019_tree_completion_to_K` | Complete profiled strict trees into actual finite K-members via compatible closed boundaries. |
| `profileTag2019_original_closed_and_coverage` | Recover original closedness and original protected-test coverage from tagged closed structures. |
| `profileRootTag2019_forget_arrow` | Recover the original Ramsey arrow from the final tagged Picture. |
| `arrow_of_BCopywiseCompletion_inClass` | Transfer arrows along maps preserving **B-copies** in an eventual K-completion. |

Generated-closure profiles may have arbitrary finite arities and
an infinite auxiliary signature. The original relational Ramsey
construction invoked by the proof is valid at that generality.
Do not silently assume every profiled intermediate structure
is canonical: the final tagged Picture is not generally a
canonical expansion, hence the two local tag-normality laws
are explicitly proved.

## The other validated main result: partial functions

```lean
#check StructuralRamsey.Structure.allThoseRamseyClasses_theorem_2_19_partialFunctions
```

The fixed 2019 partial-function application is proved in the
pinned `partite-construction` library at
`PartiteConstruction/Ramsey/AllThosePartialFiniteModels.lean`.
It uses `StructuralRamsey.Structure.Structure` and
**full functional embeddings**. For finite ordered input
structures `A,B` with each function fibre containing at
most **one** element, it constructs a finite ordered output
`C` with the same genuine partial single-valued property
and `Arrow A B C κ`.

Undefined function input tuples remain undefined under
full embeddings. This theorem differs from the general
corrected relational closure theorem and does not certify
the separate countable-target unary-function construction.

## Exported application components (no full corollary claimed)

For ordered posets:
```lean
import AllThoseRamseyClasses.Applications.PosetExactWeakCompletion
import AllThoseRamseyClasses.Applications.PosetStrongAmalgamation

#check AllThoseRamseyClasses.Applications.poset_reflexive_completion_of_exact_weak_local_tests
#check AllThoseRamseyClasses.Applications.OrderedPosets.ambient_ordered_pushout_exists
#check AllThoseRamseyClasses.Applications.OrderedPosets.orderedPosetClass_strongAmalgamation
```

The first theorem produces a genuine finite-control weak local
completion and **reflects comparisons on originally ordered pairs**.
The second produces a linear order on a strong vertex pushout
extending both side orders. The third, verified separately in PR #218,
constructs the **actual finite strong amalgam of ordered posets**,
including the induced partial-order relations. The full class-level conclusion is now separately proved by
`AllThoseRamseyClasses.Applications.OrderedPosets.orderedPoset_isRamsey`;
the exact weak local-completion bridge was discharged in PR #227.
The original paper writes reflexive $\le$, whereas the
named Lean order symbol `.lt` is **strict**. The completed class
theorem uses the equivalent strict-order representation.

For freely ordered partial Steiner triples:
```lean
import AllThoseRamseyClasses.Applications.SteinerAmbientRamsey
import AllThoseRamseyClasses.Applications.SteinerTripleIsomorphism
import AllThoseRamseyClasses.Applications.SteinerLocalCompletion

#check AllThoseRamseyClasses.Applications.SteinerTriples.orderedSteiner_isUClosed
#check AllThoseRamseyClasses.Applications.SteinerTriples.orderedSteiner_closedUHereditary
#check AllThoseRamseyClasses.Applications.SteinerTriples.orderedSteiner_isomorphismClosed
#check AllThoseRamseyClasses.Applications.SteinerTriples.orderedSteinerAmbient_isRamsey
#check AllThoseRamseyClasses.Applications.SteinerTriples.orderedSteinerClass_strongAmalgamation
#check AllThoseRamseyClasses.Applications.SteinerTriples.orderedSteiner_exactLocal_zero
#check AllThoseRamseyClasses.Applications.SteinerTriples.orderedSteiner_isRamsey
```

Covered pairs are marked by a binary predicate and determine
the exact roots of the ternary block-closure rule. A full
relational embedding in this language is a **strong**
Steiner-subsystem embedding, not an arbitrary induced
hypergraph embedding. Linear orders are arbitrary. The
Steiner **K-class** strong amalgamation, exact weak local completion
with cutoff zero, and the unconditional class Ramsey theorem are
all **verified** (PRs #235–#236). This is an auxiliary non-paper example.

For the completed paper graph, pointed-equivalence and finite-unary
applications, use `AllThoseRamseyClasses.ApplicationsAPI` and check
`PaperGraphs.freelyOrderedDigraphs_areRamsey`,
`PaperGraphs.freelyOrderedSimpleGraphs_areRamsey`,
`PaperGraphs.freelyOrderedAcyclicDigraphs_areRamsey`,
`PaperGraphs.freelyOrderedKnFreeGraphs_areRamsey`,
`PointedEquivalences.freelyOrderedPointedEquivalences_areRamsey`, and
`TotalUnaryFunctions.freelyOrderedTotalUnaryFunctions_areRamsey`.
The last theorem covers **finite B only**, not the countably infinite
B target clause of the manuscript.

For the metric and unary audits, import
`Applications.MetricJumpSandwich` and
`Applications.UnaryRootedClosureAudit`. The first proves
an algebraic idempotent sandwich lemma, not the full
$S$-metric theorem; the latter identifies an issue with an unrooted
closure-quotient shortcut, not the countable unary Ramsey
theorem.

## Machine-checked reliability and citation guidance

The source-level audit is
[`CheckAxiomsPublicAPI.lean`](../CheckAxiomsPublicAPI.lean).
The project CI builds all files in
`AllThoseRamseyClasses/`, runs every axiom checker, and
rejects `sorry`/`admit`. Green declarations permit only
`propext`, `Classical.choice` and `Quot.sound`.
This library proves the revised relational formulation with both
Definition 2.15 and Definition 2.17(4b) updated together.
Historical proof explorations have been removed from the maintained
source tree and remain available in Git history.

When citing this library, distinguish:

* **Original publication:** Hubička–Nešetřil (2019),
  Theorem 2.18 under the original wording (not the certified revised theorem);
* **Verified correction:** the *coordinated corrected
  relational* theorem exported as
  `coordinated2019_ramsey_by_profile_sparsening`;
* **Separate theorem:** finite ordered partial
  single-valued functions,
  `allThoseRamseyClasses_theorem_2_19_partialFunctions`.

For the corrected theorem's complete English proof and
the exact CI certificate see
[`docs/coordinated-profile-proof-20261013.md`](coordinated-profile-proof-20261013.md)
and [`docs/current-main-theorem-status.md`](current-main-theorem-status.md).
