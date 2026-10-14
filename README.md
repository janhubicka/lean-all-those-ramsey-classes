# All those Ramsey classes — formally validated Lean library

A Lean 4 formalization of the central definitions and Ramsey constructions
from Jan Hubička and Jaroslav Nešetřil,
[*All those Ramsey classes (Ramsey classes with closures and forbidden
homomorphisms)*](https://doi.org/10.1016/j.aim.2019.106791),
**Advances in Mathematics** 356 (2019), 106791.

**Researchers can import the corrected, unrestricted relational Ramsey theorem
as a proved Lean declaration.** This is a usable library, not merely a
collection of proposed statements and proof sketches.

> **Working manuscript and formal theorem.** During formalization,
> two definitions were adjusted together: Definition 2.15 protects exact
> induced tests which are both intrinsically U-closed and U-irreducible,
> and Definition 2.17(4b) checks membership of those same tests.
> Definition 2.17(4c) still tests **every original exact weak induced
> subset** of at most n(B,C0) vertices, without taking a closure hull.
> The Lean theorem proves this precisely stated revised formulation.
> The published wording, updated manuscript, and any future errata
> remain distinct; the repository does not announce a conclusion about
> the original wording.

The revised relational theorem has **no missing construction lemma as a
hypothesis**, no restriction on the local test cutoff, and no assumption that
the ambient Ramsey control $C_0$ is closed. It is proved via closed
Ramsey Pictures, generated-closure profiles, strict-tree sparsening and a
second fresh-root-tagged closed pass. The older generating-rank proof of
Lemma 2.30 is **not** certified by this alternative proof.

The main result is in
[`Published/Coordinated2019ProfileSparseWitness.lean`](AllThoseRamseyClasses/Published/Coordinated2019ProfileSparseWitness.lean);
the proof certificate and a complete readable proof are in
[`docs/current-main-theorem-status.md`](docs/current-main-theorem-status.md)
and [`docs/coordinated-profile-proof-20261013.md`](docs/coordinated-profile-proof-20261013.md).
For detailed theorem signatures, semantic subtleties and a migration guide,
see [**Public API reference**](docs/public-api-reference.md). The
[researcher wiki](docs/wiki/README.md) provides a paper-to-Lean theorem
crosswalk, the proof architecture, checked class examples and audit
records, following the `lean-milliken` documentation style. The [live GitHub Wiki](https://github.com/janhubicka/lean-all-those-ramsey-classes/wiki)
was published in [CI run 38642603486](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38642603486) and now synchronizes
from version-controlled Markdown.

## Find the theorem or definition you need

| You want to… | Start here |
| --- | --- |
| State the **proved** corrected 2019 Theorem 2.18 | [Main theorem](#main-proved-theorems) and `coordinated2019_theorem218` |
| Define roots, closure, weak substructures and generators | [Core mathematical objects](#core-mathematical-objects) |
| Decide which completion map is legal | [Literal versus corrected interfaces](#which-completion-and-class-predicates-should-i-use) |
| Apply the theorem to a **new class** | [Compiled class-field tutorial](#applying-the-validated-theorem-to-a-new-class) |
| Look up an exact name, namespace, import or field | [Public API reference](docs/public-api-reference.md) and [machine-checked symbol inventory](CheckAxiomsPublicAPI.lean) |
| Use the finite ordered partial-function theorem | [Theorem 2.19](#main-proved-theorems) |
| Study the proof construction | [Proof ingredients](#reusable-construction-lemmas) and [English proof](docs/coordinated-profile-proof-20261013.md) |
| Check what is verified in the examples | [Application status](#applications-verified-components-vs-open-class-corollaries) |

The single stable research import is
`AllThoseRamseyClasses.PublicAPI`. It re-exports the proved
corrected theorem and the foundational definitions in the pinned
`partite-construction` dependency. **Do not confuse “this declaration
has type `P → Q`” with a proof of `Q`**: conditional lemmas and
unproved class-instance hypotheses are kept explicit. Abandoned proof branches are removed from the maintained library;
Git history preserves their earlier versions.

## Getting started

The curated, researcher-facing import is:

```lean
import AllThoseRamseyClasses.PublicAPI

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published

#check ClosureRule
#check IsUClosed
#check IsUIrreducible
#check IsInducedClosedUHomomorphismEmbedding
#check IsCoordinated2019MultiamalgamationClass
#check coordinated2019_theorem218
#check coordinated2019_ramsey_by_profile_sparsening
```

`import AllThoseRamseyClasses` now imports the curated
`AllThoseRamseyClasses.ApplicationsAPI`, which re-exports the corrected
`PublicAPI` and fully verified concrete Ramsey-class results.
Only the maintained proof dependencies and active applications are
kept in this repository; retired proof experiments remain in Git history. Users of only the main theorem can
import `AllThoseRamseyClasses.PublicAPI`.

For an actual application, supply an ambient Ramsey class $\mathcal R$,
a target class $\mathcal K$, a closure description, the ordinary
irreducibility of $\mathcal R$, and the *corrected* class predicate:

```lean
import AllThoseRamseyClasses.PublicAPI

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published

universe u v
variable {L : RelLanguage.{u}}

example
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (hR : FiniteRamseyClass R)
    (hRIrred : ∀ {X : Type v} (C : RelStructure L X),
      R C → C.Irreducible)
    (hK : IsCoordinated2019MultiamalgamationClass R K rules) :
    FiniteRamseyClass K :=
  coordinated2019_ramsey_by_profile_sparsening R K rules hR hRIrred hK
```

**This example is itself compiled in CI**:
[`Examples/MainTheorem.lean`](AllThoseRamseyClasses/Examples/MainTheorem.lean).
It is not pseudocode. The shorter declaration
`coordinated2019_theorem218` has type
`Coordinated2019Theorem218Target`, the exact corrected universal
theorem proposition.

### Build and verify

Use the repository's pinned Lean toolchain and
[`lakefile.toml`](lakefile.toml), which pins
[`partite-construction`](https://github.com/janhubicka/partite-construction)
to a specific revision.

```sh
git clone https://github.com/janhubicka/lean-all-those-ramsey-classes.git
cd lean-all-those-ramsey-classes
lake exe cache get Mathlib.Tactic Mathlib.Data.Fintype.Pi Mathlib.Data.Fintype.Basic Mathlib.Data.Finset.Dedup
lake build AllThoseRamseyClasses
lake build AllThoseRamseyClasses.PublicAPI
lake env lean CheckAxiomsPublicAPI.lean
```

For a downstream Lake package, add this repository as a Git dependency,
pin its revision to a **commit whose full CI passed**, and import the
public API above. Do not rely on floating `main` for reproducible proofs.
See [`docs/public-api-reference.md`](docs/public-api-reference.md) for
the library's namespaces and imports.

## Core mathematical objects

All relational foundations and most reusable closure machinery live in
the pinned `partite-construction` dependency, under
`StructuralRamsey` and `StructuralRamsey.RelStructure`.
They are **re-exported** by `PublicAPI`; no second, incompatible
definition is silently introduced here.

| Definition | Meaning |
| --- | --- |
| `RelLanguage` / `RelStructure` | Relation symbols with specified finite arities / their interpretations on a vertex type; repeated entries and nullary relations are allowed. |
| `RelStructure.Embedding A B` | Injective **full** embedding; reflects as well as preserves every relational tuple. |
| `RelStructure.Irreducible A` | Every pair of distinct vertices occurs together in some positive relation tuple (complete Gaifman graph). |
| `RelStructure.IsHomomorphismEmbedding` | Positive homomorphism which is a full embedding on each ordinary irreducible induced test. |
| `StructuralRamsey.Arrow A B C κ` | Every $\kappa$-colouring of full $A$-embeddings into $C$ has a monochromatic full $B$-embedding. |
| `FiniteRamseyClass K` | For every finite $A,B\in K$ and every nonempty finite colour type, some finite $C\in K$ satisfies the arrow. |
| `ClosureRule` / `ClosureDescription` | A closure-relation symbol with a nonempty proper irreducible root / a set of such rules. |
| `IsUClosed rules A` | Exactly **one entire closure tuple** above each embedded rule root, and none above an invalid root. |
| `IsUSemiClosed rules A` | A partially defined closure relation, single-valued wherever defined; not necessarily total on roots. |
| `IsUSubstructure rules A S` | The **exact** subset $S$ contains every output of an existing closure tuple whose root is in $S$. |
| `UClosureHull rules A S` | The smallest such relative closed vertex set containing $S$; it is a *different object* from the weak test $S$. |
| `USize rules A` | Minimum cardinality of a generating set, not the number of vertices of its closure hull. |
| `IsUIrreducible rules A` | No free decomposition into two proper intrinsically $\mathcal U$-closed sides, even if $A$ itself is not closed. |

**Never interchange** ordinary irreducibility, intrinsic
$\mathcal U$-irreducibility, and the conjunction of
$\mathcal U$-closedness with $\mathcal U$-irreducibility.
Ordinary irreducibility implies intrinsic $\mathcal U$-irreducibility,
but the reverse is not automatic.

## Which completion and class predicates should I use?

The 2019 wording, the coordinated correction and an internal
embedded-test presentation are *distinct Lean interfaces*:

| Role | Main exported declaration | Exact scope |
| --- | --- | --- |
| Literal published map, **audit only** | `IsUHomomorphismEmbedding` | Protects **all** intrinsic $\mathcal U$-irreducible induced tests, even nonclosed ones. Do **not** use this as the corrected theorem hypothesis. |
| **Corrected** paper-style map | `IsInducedClosedUHomomorphismEmbedding` | Positive map; embeds precisely induced tests that are both intrinsically closed and irreducible. |
| Corrected finite $K$-completion | `HasInducedClosedUKCompletion` | Finite irreducible $K$-target; protected map from the **original weak source**. |
| Corrected local axiom | `InducedClosedULocalCompletionAt K rules B C0 n` | Tests **every original weak induced** $S$ with $\lvert S\rvert\le n$; demands a completion respecting every $B$-copy. |
| Corrected class hypothesis | `InducedClosed2019MultiamalgamationClass R K rules` | Subclass, finite, closed, induced closed-hereditary, finite strong amalgamation, and existence of a suitable local cutoff for each $B,C_0$. |
| Isomorphism invariance | `IsomorphismClosed2019 K` | Explicit assumption: bare `StructureClass` predicates are **not** automatically invariant under isomorphism. |
| **Recommended theorem hypothesis** | `IsCoordinated2019MultiamalgamationClass R K rules` | Packages the exact corrected class predicate with isomorphism invariance. |
| Internal embedded-test bridge | `IsClosedUHomomorphismEmbedding`, `ClosedUMultiamalgamationClass` | Equivalent/sufficient *working* predicates only under their proved transfer hypotheses; do not redefine the paper with these silently. |

Crucial quantifier order: **first** fix $B\in\mathcal K$
and an ambient Ramsey control $C_0\in\mathcal R$;
**then** select $n(B,C_0)$;
**then** check all original weak subsets of a candidate $C$ at that
same cutoff. No $\mathcal U$-closedness of $C_0$ is assumed.
The completion conclusion preserves copies of $B$, not necessarily
all copies of $A$ in $C$.

The exact bridge
`IsCoordinated2019MultiamalgamationClass.toAbstract`
is checked separately. For induced versus embedded hereditary
conditions, see `closedHereditary2019_iff_embedded`.

## Applying the validated theorem to a new class

For a new application, define finite relational classes
`R` (ambient) and `K` (the desired Ramsey class), with a
`ClosureDescription L`. You need to supply **all** of these
mathematical obligations; they correspond exactly to the exported
`IsCoordinated2019MultiamalgamationClass` record.

| Proof obligation | What you must establish |
| --- | --- |
| `FiniteRamseyClass R` and `R C → C.Irreducible` | The ambient relational class is Ramsey and all its members are ordinarily irreducible. |
| `subset` / `finite` | Every `K`-member belongs to `R` and has a finite carrier. |
| `closed` | Every `K`-member is intrinsically `U`-closed. |
| `hereditary` | **Exact induced** `U`-closed substructures of `K`-members remain in `K`. |
| `strong` | Real finite strong amalgamation over full `K`-members: only the prescribed common vertices overlap. |
| `localCompletion` | For **each** `B ∈ K` and **original** `C0 ∈ R`, select a fixed `n(B,C0)`. Whenever a candidate `C` has the corrected control map, closed-irreducible `K`-tests, and completions of **all original weak induced** `S` with `|S| ≤ n`, provide a `K`-completion preserving every `B`-copy. |
| `iso` | `K` is invariant under surjective full embeddings (isomorphisms). A raw Lean `StructureClass` does not guarantee this. |

Once these are proved, the theorem produces the Ramsey property
**without** an additional partite-construction hypothesis:

```lean
import AllThoseRamseyClasses.Examples.ClassApplicationBlueprint

#check AllThoseRamseyClasses.Examples.coordinated_class_of_checked_fields
#check AllThoseRamseyClasses.Examples.ramsey_of_coordinated_hypothesis
```

The full [class-field blueprint](AllThoseRamseyClasses/Examples/ClassApplicationBlueprint.lean)
is **Lean code checked by CI**, with an axiom audit. It constructs
`InducedClosed2019MultiamalgamationClass`, packages it with
`IsomorphismClosed2019` and applies
`coordinated2019_ramsey_by_profile_sparsening`. It is a
*conditional application template*, not a claim that any particular
class satisfies the listed fields.

As a concrete encoding example, [Steiner triples](AllThoseRamseyClasses/Applications/SteinerTripleClass.lean)
use a `covered` **binary root marker** and a ternary `block`
closure relation. The root is an **increasing covered pair**, not
every pair, and a full relational embedding is the intended
*strong subsystem* embedding. Its closure description is
`SteinerTriples.blockRules`; see the verified
`orderedSteiner_isUClosed`, `orderedSteiner_closedUHereditary`,
and `orderedSteinerAmbient_isRamsey` components.
The **Steiner class Ramsey corollary is not yet Lean-verified**.

For ordered posets the exact original weak-test local-completion
statement is **now proved** at `Nat.card C0`. The complete theorem
`orderedPoset_isRamsey` has no class-instance premise and is exported by
`ApplicationsAPI` (PR #227, complete CI 38633955517).

## Main proved theorems

| Statement | Declaration (namespace unless otherwise noted: `AllThoseRamseyClasses.Published`) | Status |
| --- | --- | --- |
| **Corrected unrestricted relational Theorem 2.18** | `coordinated2019_ramsey_by_profile_sparsening` | **Fully proved and CI/axiom-audited**, every fixed local cutoff. |
| The same theorem as one reusable universal proposition | `coordinated2019_theorem218` | Direct proved wrapper of `Coordinated2019Theorem218Target`, exported by `PublicAPI`. |
| Construct the unrestricted closed/sparse witness | `coordinated2019_profile_sparse_witness` | **Constructed**, not a constructor premise. |
| Corrected unrestricted initial Picture (Lemma 2.28) | `lemma_2_28_coordinated_unrestricted_induced` | **Proved** even with a nonclosed original control. |
| Induced-test to working embedded-test class transport | `coordinated2019_to_abstract_closed_class`, `IsCoordinated2019MultiamalgamationClass.toAbstract` | **Proved** with explicit isomorphism invariance. |
| Original Lemma 2.23(1) | `lemma_2_23_one` | **Proved** exact induced-set closedness iff relative $\mathcal U$-substructure. |
| Original Lemma 2.23(2) | `IsFreeAmalgam.isUClosed` (in `StructuralRamsey.RelStructure`) | **Proved**; the free-amalgam root and both sides must be $\mathcal U$-closed. |
| **Separate ordered partial-function theorem (2019 Theorem 2.19)** | `StructuralRamsey.Structure.allThoseRamseyClasses_theorem_2_19_partialFunctions` | **Proved in pinned dependency**; finite A and B, genuinely partial **single-valued** functions (empty/singleton fibres), full functional embeddings, finite ordered Ramsey witness. |
| **Finite posets with a chosen linear extension** | `AllThoseRamseyClasses.Applications.OrderedPosets.orderedPoset_isRamsey` | **Fully proved**; exact weak local completion and all class fields discharged (PR #227). |

The partial-function theorem above is an *independent free-amalgamation
application* for finite ordered partial-function structures. It is
**not** a blanket proof of the relationalization bridge needed for
every general primitive-function variant of Theorem 2.18, nor the
countably infinite-target unary-function theorem of the manuscript.

## Reusable construction lemmas

The complete main proof exports smaller results for further formal work:

* `GeneratedClosureProfile2019`,
  `closureProfileLanguage2019`,
  `closureProfileExpansion2019`:
  name an actual **closed** generated substructure of a fixed base
  by its generators; full embeddings of closed structures lift.
* `closureProfile2019_tree_completion_to_K`:
  strict trees of profiled base copies admit actual finite
  $K$-completions by strong amalgamation over a **shared full closed
  boundary**, not an assumed root-completion oracle.
* `profileTag2019_original_closed_and_coverage`,
  `profileRootTag2019_forget_arrow`:
  transfer original closure, protected tests, and Ramsey arrows back
  after the fresh-tagged final pass.
* `arrow_of_BCopywiseCompletion_inClass` (dependency):
  transfer a Ramsey arrow when only the selected $B$-copies
  survive in the completion.

These are **proof ingredients**, not alternative formulations of the
class theorem. See [the proof reference](docs/coordinated-profile-proof-20261013.md)
for their dependency order and hypotheses.

## Applications: verified components vs. open class corollaries

We explicitly distinguish a proved *application component* from a
fully verified Ramsey statement for that class. Import only the
relevant application module:

| Application | Verified entry points | What is **not yet certified** |
| --- | --- | --- |
| **Ordered posets with a linear extension** | `Applications/PosetRamseyTheorem.lean`: `orderedPoset_exactLocalAtControlCard`, `orderedPoset_isCoordinated2019Multiamalgamation`, `orderedPoset_isRamsey` | **The full Ramsey class is verified** (PR #227, CI 38633955517). The exact local cutoff is `Nat.card C0`; `.lt` denotes strict order although the manuscript uses reflexive $\le$. |
| **Freely ordered partial Steiner triples, strong embeddings** | `SteinerTripleClass.lean`, `SteinerFreeAmalgamClosure.lean`, `SteinerOrderPushout.lean` and other component files | Closure of free strong-root amalgams (PR #228) and arbitrary compatible vertex orders (PR #229) are checked. Full block/relation normal forms, exact local completion and final class Ramsey theorem are still open. |
| **Jump-distance metric lemma** | `MetricJumpSandwich.lean`: `sandwich_constant_on_parts` | Its exact $\oplus_S$ specialization and full convexly ordered $S$-metric Ramsey theorem. |
| **Unary-function quotient counterexample** | `UnaryRootedClosureAudit.lean`: `naive_unrooted_closure_not_injective` | The rooted-quotient Ramsey construction, especially for countable targets. |

The [manuscript applications ledger](https://github.com/janhubicka/All-those-Ramsey-classes/blob/main/APPLICATIONS-VALIDATION-2026-10-14.md)
tracks remaining application-specific corrections. **Do not cite a
verified component as if it were the final application Ramsey theorem.**

## Audit, reliability and historical status

Each repository change is built by
[GitHub Actions](.github/workflows/lean.yml), which:

1. builds `AllThoseRamseyClasses` **and all Lean files** under
   `AllThoseRamseyClasses/`, even if not in the umbrella import;
2. runs every `CheckAxioms*.lean` and
   [`scripts/check_axioms.py`](scripts/check_axioms.py);
3. verifies the reachable proof/active-application module graph;
4. runs the entire-source import, axiom-declaration and admission audit
   `python3 scripts/audit_library.py`, preserving optional research modules;
5. independently runs the deletion/reachability invariant
   `scripts/cleanup_inventory.py --verify`, and rejects any admissions.

Only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` are permitted for green theorems. A checked theorem
with an **unproved assumption** is still only conditional. A green
result about the corrected definitions does not retroactively verify
the literal published theorem or its original proof. For provenance:

* [Current checked endpoint and CI certificate](docs/current-main-theorem-status.md)
* [Full English profile/sparsening proof](docs/coordinated-profile-proof-20261013.md)
* [Revised definitions and precise theorem scope](docs/wiki/Published-statements.md)
* [Public API and symbol/reference guide](docs/public-api-reference.md)
* [Research wiki: statements, applications, proof architecture and audits](docs/wiki/README.md)
* [Separate manuscript and reversible correction history](https://github.com/janhubicka/All-those-Ramsey-classes)

The literature often cites Theorem 2.18 without specifying its
completion-map semantics. **When using this formal result, state that
you use the coordinated corrected relational version and explicitly
verify its isomorphism invariance and exact local-completion axiom.**
