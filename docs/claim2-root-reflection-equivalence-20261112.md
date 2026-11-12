# Track C: exact equivalence of Q root reflection and full-seam injectivity

**12 November 2026. Draft; require exact-head full Lean CI and axiom checks.**

## Setting

A genuine native functional source flip builds New as a full free amalgam
of rooted replacement Q with old complement E. Both old and new include
the same full E; their weak target maps have *exactly* the same
coordinates on all of E. The Q source map factors through the Left
target witness: `flip(iQ q)=jLeft(gQ q)`. On the Q common root,
the piece map has the prescribed exact coordinates,
`gQ(qRoot r)=iLeft r`. Assume the **old** full seam-preimage
is injected by the old weak target map (no extra global injection).

## New equivalence

The **new** full seam-preimage is injected by `flip`
**if and only if** the Q piece map reflects the Left common root:

```text
∀ q, gQ q ∈ range(iLeft) → q ∈ range(qRoot)
```

The forward implication does **not** require old source injectivity.
A Q nonroot with target in the common root collides with the
corresponding Q root vertex, violating new seam injectivity.

For the reverse, root reflection excludes every Q-only vertex
mapping into the target seam: a root Q vertex belongs to E by
the exact new full free-amalgam overlap. The already kernel-
checked `fullNativeReplacement_seamInjective_of_noFreshSeam`
then rules out all new seam collisions.

The API exports the two implications and their equivalence, with
three named `#print axioms` audit roots.

## What is *not* proved

Selected canonical Q's piece map `gQ` is a **weak EHN**
homomorphism-embedding, and root reflection does not currently
follow from that predicate. The equivalence is an exact reduction,
not an unconditional iteration theorem or a new global strong
amalgamation proof. A future construction must either establish
root reflection for an appropriately selected Q, or replace
the current rank/state method to tolerate root-reflection defects.
No weak source quotient, distinct-target-image counts, or
unfounded new global injectivity is invoked.

Numbered 2019 paper remains frozen; removed collaborator TODOs
are not reintroduced.
