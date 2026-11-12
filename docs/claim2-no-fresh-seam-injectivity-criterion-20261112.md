# Track C — a conditional seam-injectivity preservation criterion

**12 November 2026. Draft stacked on #1043; full exact-head Lean CI required.**

In an actual native full free-amalgam source flip let E be the unchanged
complement and Q the replacement side. The same old/new structural
E embeddings preserve every source point in E, and the old/new weak
target maps agree on the entire embedded E exactly.

Assume that the old weak map is injective on the **entire** preimage
of the target common seam. Draft #1043 (collision localization) proves
that each pair of distinct new seam preimages with equal target value
contains a source point in the new Q image **outside** the E image.

This new theorem, `fullNativeReplacement_seamInjective_of_noFreshSeam`,
adds one explicit sufficient condition:

> Every newly inserted Q-side vertex outside retained E maps
> outside the common target seam.

Then the entire new seam preimage is injected by the weak target map;
otherwise its collision would violate the fresh-side condition.
This is stronger than merely retaining original ordered outer-root
target coordinates.

**Unresolved applicability:** the existing original-2019 canonical
selected-Q replacement does not establish the no-fresh-seam condition;
newly inserted Q vertices MAY have seam-valued weak targets.
It would be incorrect to infer this condition from old root-image
injectivity or exterior SOURCE-count conservation. The lemma isolates
one precise auxiliary property sufficient for iteration, not a proof
that it holds for all actual source flips.

No global image quotient, no source supports counted by distinct
target images, no manuscript changes and no collaborator-removed
TODOs reintroduced. Exact-head full Lean build, no-admission,
protected-root inventory and permitted-axiom audit are required.
