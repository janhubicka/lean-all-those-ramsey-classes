# Track C — exact Q root-reflection defect in a new seam collision

**12 November 2026. Draft stacked on #1043; exact-head Lean CI required.**

A genuine complete native selected-Q replacement provides:

- Old and new FULL functional embeddings of the retained complement E;
- a full new source decomposition as the free amalgam Q +_Root E;
- the weak target-map equality on all of E;
- a piece-level weak EHN map `gQ : Q.Carrier → Left.Carrier`;
- `flip(iQ q) = jLeft(gQ q)` for all genuine Q source vertices.

Under the sole **old** assumption that the original weak target map
is injective on its complete target-common-seam preimage, the pending
#1043 localization shows a NEW seam collision must involve a Q-only
vertex `iQ q` outside the embedded E. The free-amalgam overlap
equivalence implies such `q` is **not** in Q's embedded root.
Its new target is in `range(jLeft.comp iLeft)`, so the piece map
`gQ q` belongs to the embedded root of Left. Thus:

  q ∉ range(Q.rootEmbedding)
  gQ q ∈ range(iLeft)

This is an actual source-side **root-reflection defect**.
The new theorem proves that any new seam collision yields one;
it does NOT rule defects out, and does NOT promote a generic weak
homomorphism-embedding to a full injective embedding.

Why this matters: the printed Claim 2 iteration requires
injectivity of the full seam preimage at repeated stages, while
current canonical selected-Q replacement only guarantees ordered
outer-root target coordinates. It also returns `gQ` without a
root-reflection certificate. We now have an exact *local* proof
target: exclude these Q-nonroot-to-Left-root vertices, or construct
a replacement/normalization handling them without changing the
unchanged full complement.

This is not a new solution of unrestricted strong amalgamation.
Frozen 2019 prose untouched; no removed TODOs added.
