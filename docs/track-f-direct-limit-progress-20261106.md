# Track F — exact direct-limit boundary (6 November 2026)

This note records the distinction between **kernel-verified finite-age
infrastructure**, **new proof candidates awaiting CI**, and the actual
remaining infinite Fraïssé-limit obligations for the original
root-injective maximal forbidden-piece lift of *All Those Ramsey
Classes* (2019). The numbered manuscript `ramsey.tex` is frozen.

## Certified earlier in Track F

The following are merged with complete Lean, permitted-axiom and
admission-source checks:

- **#742**: hereditary original maximal-trace age, full JEP and
  exact-overlap strong AP **conditional** on original
  `GlobalCanonicalShadowFreeAmalgamation`.
- **#778**: an actual empty-carrier age member for regular families
  of nonempty connected forbidden sources.
- **#787 and #798**: finite genuine labelled expansion fibres and
  countable, FULL-isomorphism representatives in a finite old
  relation/function signature.
- **#804**: a countable original global lift signature even when
  regular forbidden families have infinitely many piece types
  and unbounded root widths.
- **#807 and #821**: the exact full-JEP criterion. Under regularity
  and full native heredity, maximal-trace JEP iff native JEP.
  With the STILL OPEN general original shadow-avoidance premise
  supplied, the finite Fraïssé-age input is equivalent to native
  JEP. The empty forbidden family with an old nullary relation
  can fail full JEP. The separate manuscript TODO is ATRC-073.
- **#825, #832, #836, #841**: finite extension and cofinality
  schedulers plus countable genuine full extension diagrams.
- **#842, #845, #852**: an ACTUAL nat-indexed chain of finite
  maximal-trace age members, fair finite repetition of each
  extension diagram, and full maps from earlier to later stages.
- **#837 and #848**: exactly faithful first-order relational graph
  encoding for complete native partial/set-valued function
  outputs. A first-order graph embedding reconstructs a FULL
  native functional embedding if and only if its image is
  function-output closed; mere induced graph structure is
  insufficient.

These statements do **not** produce a Fraïssé limit or remove the
original Claim 2 / shadow-avoidance hypothesis.

## Active proof work: keep all marks orange until complete CI

1. **#857, `GlobalFiniteTraceChainCoherence.lean`**:
   prove `e_{m,k} = e_{n,k}.comp e_{m,n}`.
   The earlier induction failed due the dependent `Nat.leRecOn`
   successor equation, **not** a mathematical counterexample.
   The revised proof invokes `Nat.leRecOn_succ h` explicitly
   and is still CI-pending. Without this, neither quotient
   direct-limit construction should be called verified.
2. **#900, `GlobalOriginalTraceDirectLimitCarrier.lean`**,
   stacked on #857: build a real `DirectedSystem` of vertex
   maps, quotient its tagged finite carriers by eventual
   agreement, prove countability and injectivity of each
   canonical stage inclusion. **No structure interpretation**.
3. **#901, `GlobalFiniteTraceChainFibreStability.lean`**,
   independent: for every old input tuple at stage m and n≥m,
   the ENTIRE later function fibre over its image equals
   the direct image of the old fibre. Also isolate the
   full function-closed-map property and bidirectional
   relation reflection. This statement includes nullary
   symbols, empty fibres, multi-valued outputs and repeated
   coordinates.
4. **#903, `GlobalOriginalTraceFirstOrderDirectLimit.lean`**,
   stacked on #900/#857: convert the same full stage maps
   to first-order graph embeddings, instantiate a genuine
   directed system, and invoke the verified Mathlib
   `FirstOrder.Language.DirectLimit` to construct a real
   relational graph model and canonical FIRST-ORDER
   stage embeddings. A closed-image theorem is **not**
   part of #903 yet.

All four PRs have their own named `#print axioms` checks
and active roots. Only completed full CI verifies a
candidate; a run at the global axiom phase is not green.

## Why two quotient carriers currently appear

The generic quotient in #900 is useful for independent
countability and injectivity lemmas. Mathlib's first-order
direct limit in #903 is useful because it already constructs
the full relational interpretation and canonical first-order
embeddings.

These quotient presentations are naturally isomorphic:
they identify the SAME tagged stage vertices under the
SAME eventual agreement of the FULL transition maps.
Before exposing a public infinite-model API, choose ONE
carrier presentation as canonical, or prove the explicit
equivalence and use it to transport the model structure.
Avoid maintaining duplicate unrelated limit structures.

## Exact next theorem: stage images are function-closed in the limit

Let `M_graph` be the Mathlib first-order graph direct limit
and `u_m : X_m → M_graph` its canonical first-order stage
embedding. For every function symbol F, stage input tuple
`x : Fin (arity F) → X_m`, and output `y ∈ M_graph`,
the essential target lemma is

```
  M_graph.Rel (graph F) (append (u_m ∘ x) y)
    ↔ ∃ z ∈ (X_m).func F x, u_m z = y
```

Here `graph F` has arity `arity F + 1`. The forward
direction is the substantial one: any graph incidence in
the direct limit has witnesses at some common finite stage
n≥m. The verified no-new-output property of each full
stage map, applied at n, pulls that output back to an
actual element of the original fibre in `X_m`.
The reverse direction is direct preservation of the
graph relation by the first-order stage embedding.

This is precisely `Structure.ClosedMap` for the
canonical stage inclusion. By the verified #848 bridge,
that condition promotes `u_m` to a genuine FULL native
functional embedding into `Structure.ofGraph M_graph`.
No first-order arbitrary-substructure inheritance claim
should be inserted along the way.

Once this is established, formalize age equality, the
finite extension property using the fair chain schedule,
then back-and-forth ultrahomogeneity. Explicitly keep the
unrestricted original shadow-avoidance/Claim 2 theorem
and the final ordered Ramsey-local completion theorem
as separate upstream obligations.

## Manuscript control

ATRC-073 now records the certified #807 age-level
nullary obstruction. The printed arity convention must
still be checked. `ramsey.tex` is untouched; no green
validation marker is justified for unrestricted Section 3
or for the as-yet unformalized infinite Fraïssé limit.
