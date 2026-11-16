# Track B: A-free SAME selected-Q source cost, and lex-minimal obstruction

15 November 2026. Stacked draft on #1241 → #1237 → #1231.
The frozen numbered 2019 manuscript is unchanged.

## Adversarial proof-control gap fixed

The merged weaker `claim2NativeSelectedQProvenanceStep` predicate
records the real forbidden selected Q, its FULL native Q+old E
free-amalgam, exact retained E target-map agreement, local strict
B-source rank descent, exterior source support, root coordinates
and surviving A-anchor. It does **not** record that the REMOVED
OLD selected component was A-free. Therefore one cannot
legitimately instantiate the merged Track C exact A-source
cost formula on an arbitrary edge of that weaker relation.

New `Claim2AFreeSelectedQCostCertificate.lean` defines the
STRICTLY STRONGER `claim2NativeAFreeSelectedQStep`, which
records the A-freeness of the SAME old selected inner source
component as the Q+E provenance certificate. It proves:

- Every genuinely eligible one-sided B-active inner separator
  admits ONE same-Q native state replacement whose exact
  free diagram **and old A-freeness** are both stored.
- Forgetting only A-freeness recovers the merged weaker
  `claim2NativeSelectedQProvenanceStep`.
- For any such stronger step, the merged exact native
  cardinality calculation gives
  `total A(new) = total A(old) + Q-private A(new)`
  counting LITERAL source vertices (not target-image count).
  This is the precise A-support increase cost of Q.
- For a globally lexicographically (A-source,B-source)
  MINIMAL ORIGINAL forbidden EHN witness, a genuine
  B-decreasing A-free same-Q step MUST have a
  POSITIVE number of inserted Q-private A-exclusive source
  vertices. Proof: the old lex minimizer and merged strict
  global B-source decrease force STRICT global A increase;
  exact same-Q A-cost equality identifies its positive
  source-cardinality contribution.

**Critical conclusion:** The raw Q provenance relation did
not, by itself, justify treating every step as A-free or
A-neutral. The stronger theorem gives the exact extra
certificate required by the sharp `Claim2SelectedQAactive...`
source-count lemmas. It does NOT show that the inserted
selected Q can always be made A-neutral, or that all intermediate
source witnesses remain original A-minimal, or that
root/boundary collisions and old-root capture/A-mixedness
are impossible. In fact the lex-minimal theorem shows that
an A-NEUTRAL successful Q-step at an original lex minimum
would be contradictory to strict global B decrease.

One new source module, named kernel axioms checks, protected
active proof root. Hold DRAFT until exact-head Lean/Lake,
allowed axiom/admission/import/source-contract/inventory CI
and stacked parents pass. No new axiom, weak-image quotient,
second arbitrary Q, or frozen text edits.
