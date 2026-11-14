# Track B/C: positive-rank actual flip or two precise smaller-root defects

**13 November 2026.** This new source-side Lean theorem is stacked
on Track C's draft #1133, whose conditional smaller-root B→A flip
is the necessary mathematical input. The original 2019 TeX remains frozen.

## Decomposition of the failure of positive-rank descent

The main verified conditional active-boundary theorem gives either
a genuinely selected Q B→A flip with STRICTLY smaller interior
B-exclusive SOURCE rank, original GLOBAL selected symbol, exact
all-target exterior SOURCE support, actual new geometric outer
piece and surviving A-exclusive SOURCE anchor, or a genuine smaller
positive native geometric separator component d.

In the smaller-root alternative, the returned root lies in the
full generated boundary T of a B-exclusive component in the old P,
so `Set.InjOn f T` follows from the active-boundary hypothesis.
Consequently the entire ordered `Fin m` target-root tuple of d
is INJECTIVE, even if the whole target seam is not.

The other checked conditional input, Track C #1133, proves:
if d's selected component captures NONE of the old P-root
vertices, and contains NO A-exclusive source vertex, it is an
ACTUAL proper one-sided inner geometric piece and admits the
SAME-selected-Q replacement with ALL exterior-count/anchor
invariants required by the successful branch.

The resulting new theorem
`claim2_positiveRank_actualStep_or_oldRootCapture_or_AMixed_of_activeBoundaryInj`
refines the smaller-root alternative into two explicit
certificates, while leaving the flip output unchanged:

* **Old-root capture:** a literal i:Fin n with P.roots i
  belonging to d's selected SOURCE component;
* **A-mixedness:** a literal SOURCE vertex z in that component
  with f z in the target A/Left-exclusive part.

If neither certificate exists, use #1133 to return an ACTUAL
same-selected-Q rank-decreasing B-to-A flip. This is a genuine
statement about original source geometry, not a manipulated
weak-image quotient or a new admissibility oracle.

## Adversarial scope

Neither old-root capture nor A-mixedness has been ruled out,
nor shown to produce a well-founded alternative measure.
The initial selected outer root tuple target injection and
initial B-active boundary injection remain independent
hypotheses, and the terminal A-source minimizer exit has not
yet been instantiated. No full seam injection is assumed,
and the source-root cardinality m need not be smaller than n.
This theorem does not establish unrestricted Claim 2.

## CI and document controls

Do not merge until parent #1133 is exact-head green and merged,
then retarget to main. This PR additionally needs exact-head
full Lean/Lake build, permitted-axiom inventory, named
`#print axioms`, active-root contract/source integrity and
no-admissions checks. No change to original numbered ramsey.tex,
no restoration of collaborator-removed TODOs.
