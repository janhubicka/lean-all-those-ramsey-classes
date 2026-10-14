# All those Ramsey classes — formally validated Lean library

A Lean 4 formalization of the central definitions and Ramsey constructions
from Jan Hubička and Jaroslav Nešetřil,
[*All those Ramsey classes (Ramsey classes with closures and forbidden
homomorphisms)*](https://doi.org/10.1016/j.aim.2019.106791),
**Advances in Mathematics** 356 (2019), 106791.

**Researchers can import the corrected, unrestricted relational Ramsey theorem
as a proved Lean declaration.** This is a usable library, not merely a
collection of proposed statements and proof sketches.

> **Important correction to the 2019 statement.**
> The *literal* published Theorem 2.18 is **refuted** by Lean-checked
> counterexamples. The library proves a **coordinated correction** changing
> *both* the protected-map tests of Definition 2.15 and the membership tests
> of Definition 2.17(4b) to structures that are **simultaneously intrinsically
> \(\mathcal U\)-closed and \(\mathcal U\)-irreducible**. The original
> Definition 2.17(4c) still tests **every exact weak induced subset of at
> most \(n(B,C_0)\) vertices**. It does *not* replace that subset by its
> generated closure. This distinction is indispensable when applying or
> citing the theorem.

The revised relational theorem has **no missing construction lemma as a
hypothesis**, no restriction on the local test cutoff, and no assumption that
the ambient Ramsey control \(C_0\) is closed. It is proved via closed
Ramsey Pictures, generated-closure profiles, strict-tree sparsening and a
second fresh-root-tagged closed pass. The older generating-rank proof of
Lemma 2.30 is **not** certified by this alternative proof.

The main result is in
[`Published/Coordinated2019ProfileSparseWitness.lean`](AllThoseRamseyClasses/Published/Coordinated2019ProfileSparseWitness.lean);
the proof certificate and a complete readable proof are in
[`docs/current-main-theorem-status.md`](docs/current-main-theorem-status.md)
and [`docs/coordinated-profile-proof-20261013.md`](docs/coordinated-profile-proof-20261013.md).
For detailed theorem signatures, semantic subtleties and a migration guide,
see [**Public API reference**](docs/public-api-reference.md).

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

`import AllThoseRamseyClasses` also imports this public API and retains
the historical/counterexample modules for backward compatibility.
A researcher only using the corrected result can instead import
`AllThoseRamseyClasses.PublicAPI` to avoid conflating the literal,
refuted formulation with the proved one.

For an actual application, supply an ambient Ramsey class \(\mathcal R\),
a target class \(\mathcal K\), a closure description, the ordinary
irreducibility of \(\mathcal R\), and the *corrected* class predicate:

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
| `StructuralRamsey.Arrow A B C κ` | Every \(\kappa\)-colouring of full \(A\)-embeddings into \(C\) has a monochromatic full \(B\)-embedding. |
| `FiniteRamseyClass K` | For every finite \(A,B\in K\) and every nonempty finite colour type, some finite \(C\in K\) satisfies the arrow. |
| `ClosureRule` / `ClosureDescription` | A closure-relation symbol with a nonempty proper irreducible root / a set of such rules. |
| `IsUClosed rules A` | Exactly **one entire closure tuple** above each embedded rule root, and none above an invalid root. |
| `IsUSemiClosed rules A` | A partially defined closure relation, single-valued wherever defined; not necessarily total on roots. |
| `IsUSubstructure rules A S` | The **exact** subset \(S\) contains every output of an existing closure tuple whose root is in \(S\). |
| `UClosureHull rules A S` | The smallest such relative closed vertex set containing \(S\); it is a *different object* from the weak test \(S\). |
| `USize rules A` | Minimum cardinality of a generating set, not the number of vertices of its closure hull. |
| `IsUIrreducible rules A` | No free decomposition into two proper intrinsically \(\mathcal U\)-closed sides, even if \(A\) itself is not closed. |

**Never interchange** ordinary irreducibility, intrinsic
\(\mathcal U\)-irreducibility, and the conjunction of
\(\mathcal U\)-closedness with \(\mathcal U\)-irreducibility.
Ordinary irreducibility implies intrinsic \(\mathcal U\)-irreducibility,
but the reverse is not automatic.

## Which completion and class predicates should I use?

The 2019 wording, the coordinated correction and an internal
embedded-test presentation are *distinct Lean interfaces*:

| Role | Main exported declaration | Exact scope |
| --- | --- | --- |
| Literal published map, **audit only** | `IsUHomomorphismEmbedding` | Protects **all** intrinsic \(\mathcal U\)-irreducible induced tests, even nonclosed ones. Do **not** use this as the corrected theorem hypothesis. |
| **Corrected** paper-style map | `IsInducedClosedUHomomorphismEmbedding` | Positive map; embeds precisely induced tests that are both intrinsically closed and irreducible. |
| Corrected finite \(K\)-completion | `HasInducedClosedUKCompletion` | Finite irreducible \(K\)-target; protected map from the **original weak source**. |
| Corrected local axiom | `InducedClosedULocalCompletionAt K rules B C0 n` | Tests **every original weak induced** \(S\) with \(|S|\le n\); demands a completion respecting every \(B\)-copy. |
| Corrected class hypothesis | `InducedClosed2019MultiamalgamationClass R K rules` | Subclass, finite, closed, induced closed-hereditary, finite strong amalgamation, and existence of a suitable local cutoff for each \(B,C_0\). |
| Isomorphism invariance | `IsomorphismClosed2019 K` | Explicit assumption: bare `StructureClass` predicates are **not** automatically invariant under isomorphism. |
| **Recommended theorem hypothesis** | `IsCoordinated2019MultiamalgamationClass R K rules` | Packages the exact corrected class predicate with isomorphism invariance. |
| Internal embedded-test bridge | `IsClosedUHomomorphismEmbedding`, `ClosedUMultiamalgamationClass` | Equivalent/sufficient *working* predicates only under their proved transfer hypotheses; do not redefine the paper with these silently. |

Crucial quantifier order: **first** fix \(B\in\mathcal K\)
and an ambient Ramsey control \(C_0\in\mathcal R\);
**then** select \(n(B,C_0)\);
**then** check all original weak subsets of a candidate \(C\) at that
same cutoff. No \(\mathcal U\)-closedness of \(C_0\) is assumed.
The completion conclusion preserves copies of \(B\), not necessarily
all copies of \(A\) in \(C\).

The exact bridge
`IsCoordinated2019MultiamalgamationClass.toAbstract`
is checked separately. For induced versus embedded hereditary
conditions, see `closedHereditary2019_iff_embedded`.

## Main proved theorems

| Statement | Declaration (namespace unless otherwise noted: `AllThoseRamseyClasses.Published`) | Status |
| --- | --- | --- |
| **Corrected unrestricted relational Theorem 2.18** | `coordinated2019_ramsey_by_profile_sparsening` | **Fully proved and CI/axiom-audited**, every fixed local cutoff. |
| The same theorem as one reusable universal proposition | `coordinated2019_theorem218` | Direct proved wrapper of `Coordinated2019Theorem218Target`, exported by `PublicAPI`. |
| Construct the unrestricted closed/sparse witness | `coordinated2019_profile_sparse_witness` | **Constructed**, not a constructor premise. |
| Corrected unrestricted initial Picture (Lemma 2.28) | `lemma_2_28_coordinated_unrestricted_induced` | **Proved** even with a nonclosed original control. |
| Direct restricted fixed-cutoff Ramsey result | `coordinated2019_cutoff_three_unrestricted_induced` | **Proved** for \(n\le3\); superseded in generality by the unrestricted theorem. |
| Induced-test to working embedded-test class transport | `coordinated2019_to_abstract_closed_class`, `IsCoordinated2019MultiamalgamationClass.toAbstract` | **Proved** with explicit isomorphism invariance. |
| Original Lemma 2.23(1) | `lemma_2_23_one` | **Proved** exact induced-set closedness iff relative \(\mathcal U\)-substructure. |
| Original Lemma 2.23(2) | `IsFreeAmalgam.isUClosed` (in `StructuralRamsey.RelStructure`) | **Proved**; the free-amalgam root and both sides must be \(\mathcal U\)-closed. |
| **Separate ordered partial-function theorem (2019 Theorem 2.19)** | `StructuralRamsey.Structure.allThoseRamseyClasses_theorem_2_19_partialFunctions` | **Proved in pinned dependency**; finite A and B, genuinely partial **single-valued** functions (empty/singleton fibres), full functional embeddings, finite ordered Ramsey witness. |

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
  \(K\)-completions by strong amalgamation over a **shared full closed
  boundary**, not an assumed root-completion oracle.
* `profileTag2019_original_closed_and_coverage`,
  `profileRootTag2019_forget_arrow`:
  transfer original closure, protected tests, and Ramsey arrows back
  after the fresh-tagged final pass.
* `arrow_of_BCopywiseCompletion_inClass` (dependency):
  transfer a Ramsey arrow when only the selected \(B\)-copies
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
| **Ordered posets with a linear extension** | `Applications/OrderedPosetClass.lean`, `PosetAmalgamationOrder.lean`, `PosetGlobalQuasiCycle.lean`, `PosetExactWeakCompletion.lean`, `PosetStrongAmalgamation.lean` | **Strong amalgamation is proved** (`orderedPosetClass_strongAmalgamation`, CI-green PR #218). Still missing: assembled exact corrected local-completion class instance and final Ramsey declaration. The relation `.lt` is strict even when the manuscript uses reflexive \(\le\). |
| **Freely ordered partial Steiner triples, strong embeddings** | `SteinerTripleClass.lean`, `SteinerStrongEmbedding.lean`, `SteinerTripleIsomorphism.lean`, `SteinerAmbientRamsey.lean` | Actual strong-amalgamation, local-completion and final class theorem. The binary *covered-pair* marker makes embeddings strong; arbitrary orders are allowed. |
| **Jump-distance metric lemma** | `MetricJumpSandwich.lean`: `sandwich_constant_on_parts` | Its exact \(\oplus_S\) specialization and full convexly ordered \(S\)-metric Ramsey theorem. |
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
3. runs finite regression checks, including literal counterexamples;
4. rejects source admissions such as `sorry` and `admit`.

Only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` are permitted for green theorems. A checked theorem
with an **unproved assumption** is still only conditional. A green
result about the corrected definitions does not retroactively verify
the literal published theorem or its original proof. For provenance:

* [Current checked endpoint and CI certificate](docs/current-main-theorem-status.md)
* [Full English profile/sparsening proof](docs/coordinated-profile-proof-20261013.md)
* [Literal 2019 counterexample](docs/literal-counterexample.md)
* [Public API and symbol/reference guide](docs/public-api-reference.md)
* [Separate manuscript and reversible correction history](https://github.com/janhubicka/All-those-Ramsey-classes)

The literature often cites Theorem 2.18 without specifying its
completion-map semantics. **When using this formal result, state that
you use the coordinated corrected relational version and explicitly
verify its isomorphism invariance and exact local-completion axiom.**
