# Published paper and the Lean-verified formulation

This page describes the relationship between Hubička–Nešetřil,
*All those Ramsey classes* (2019), the working revised manuscript,
and the formalized results. During formalization, **two definitions
were adjusted together**. The theorem proved in Lean uses those
revised definitions. The original published text and the revised
manuscript must not be conflated, but this page **does not assert a
verdict about the original formulation**. Author review and any
decision to publish errata are separate from the proof certificate.

## Exactly which definitions changed?

1. **Definition 2.15, protected homomorphism-embeddings.**
   The working revision asks that the map restrict to an embedding
   on every *induced* substructure that is both intrinsically
   \(\mathcal U\)-closed and \(\mathcal U\)-irreducible.
   The original wording tested intrinsic \(\mathcal U\)-irreducibility
   without the additional closedness condition.
2. **Definition 2.17(4b), membership tests.**
   The working revision likewise requires membership in \(\mathcal K\)
   for substructures that are both intrinsically
   \(\mathcal U\)-closed and \(\mathcal U\)-irreducible.
   The two changes are coordinated; they define the hypothesis
   used by the certified Lean theorem.

**Unchanged:** Definition 2.17(4a) retains the original ambient
control \(C_0\), which need not be closed. Clause (4c) still checks
**all original exact weak induced subsets** \(S\) with
\(|S|\le n(B,C_0)\), including nonclosed sets. Neither S nor C0
is replaced by its generated closure. The fixed cutoff is selected
for B and C0 before verifying the weak candidate C.

These distinctions are essential to reproduce the Lean theorem's
actual hypotheses. Restricting protected tests weakens the map
condition; in the local-completion *implication*, the revised
antecedent becomes easier to satisfy, so the class hypothesis
becomes stronger. Isomorphism invariance is explicitly packaged
by `IsCoordinated2019MultiamalgamationClass`.

## Mathematically verified endpoints

| Paper topic | Lean declaration | What is certified |
| --- | --- | --- |
| Closure descriptions and roots | `ClosureRule`, `ClosureDescription`, `IsUClosed` | Working relational representation |
| Intrinsic irreducibility | `IsUIrreducible` | Intrinsic, distinct from ordinary irreducibility and from closedness |
| Revised Definition 2.15 | `IsInducedClosedUHomomorphismEmbedding` | Exact induced closed-and-irreducible protected maps |
| Revised Definition 2.17 | `InducedClosed2019MultiamalgamationClass` | Coordinated membership tests and unchanged exact weak-subset cutoff |
| **Theorem 2.18, working revised formulation** | `coordinated2019_theorem218` | **Proved**, for arbitrary fixed cutoff |
| Theorem 2.19, finite ordered partial functions | `allThoseRamseyClasses_theorem_2_19_partialFunctions` | Proved in pinned dependency |
| Lemma 2.23(1) | `lemma_2_23_one` | Closedness and exact induced subsets |
| Lemma 2.23(2) | `IsFreeAmalgam.isUClosed` | Closure of a free amalgam over a closed common root |
| Lemma 2.28, revised closed-test Picture | `lemma_2_28_coordinated_unrestricted_induced` | Proved |
| Lemma 2.29, revised closed-test coverage | `lemma_2_29_coordinated_induced_full` | Proved |
| Lemma 2.30, original rank-increment proof | Manuscript proof | Separate proof audit; not established by the alternative construction |
| Posets with chosen linear extension | `orderedPoset_isRamsey` | Full class-level Ramsey theorem proved |
| Ordered Steiner triples | `Steiner*` application components | Only identified components proved; class conclusion pending |

The main theorem proof constructs its profile/sparsening witness:
it does **not** posit a rank increment or compatible closed boundary
as an extra assumption, and it does not impose closedness on C0.

## Manuscript and possible errata

The mathematical source is being kept as a *working revised manuscript*
with reversible changes, TODOs and accurately scoped validation marks.
The corrected proof and the manuscript's original native
generating-rank argument are distinct: verifying the former does not
establish every step of the latter. The two revisions of the
definitions will be explained alongside the fixed manuscript.
Whether to publish a separate erratum is a later decision with
the authors; neither a positive certification nor a negative
judgement about the original wording is stated here.

Proof certificate:
[PR #195](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/195)
and [full CI 38479503776](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38479503776).
The completed poset application:
[PR #227](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/227),
[CI 38633955517](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38633955517).
