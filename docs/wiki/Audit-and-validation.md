# Validation and maintainability audit

The library distinguishes a kernel-checked Lean theorem from the
editorial relationship between its definitions and the published
2019 article. During verification, Definitions 2.15 and 2.17(4b)
were adjusted in the working manuscript to test structures that
are simultaneously intrinsically U-closed and U-irreducible.
Clause (4c) continues to quantify over **all original weak induced
subsets**, without passing to a closure hull. The verified theorem
has precisely these revised hypotheses. Questions about the earlier
wording belong to author review of the revised manuscript, not
to the public status table.

## Mathematical referee checks

* Select the cutoff \(n(B,C_0)\) only after fixing B and the
  **original** ambient Ramsey control C0. C0 may be nonclosed.
  Test every original weak induced set S with \(|S|\le n\).
* Keep ordinary irreducibility, intrinsic U-irreducibility,
  and intrinsic U-closedness separate.
* A protected completion map need not be globally injective;
  its required restrictions are full induced embeddings.
* The verified alternative profile proof uses actual closed
  boundaries, finite strict-tree completions and a second
  fresh-root-tagged pass. It does not certify the manuscript's
  separate native Lemma 2.30 generating-rank argument.
* A Ramsey-class application becomes certified only when all
  class hypotheses, including exact local completion, have
  been proved. Ordered posets have a complete endpoint;
  ordered Steiner triples remain a partial application.

## Proof integrity

GitHub Actions builds the curated library and individual retained
modules, checks their protected-root reachability, then compiles the named `CheckAxioms*.lean` endpoints.
The permitted axioms are `propext`, `Classical.choice` and
`Quot.sound`. The import and source audit rejects missing
imports, cycles, `sorry`, `admit` and additional local axioms.
A finite regression or a conditional blueprint is not by
itself a proof of an unconditional class theorem.

## Dead-end cleanup policy

The source tree keeps the transitive proof dependencies of the
completed relational theorem, reusable class examples and
actively developed applications. Obsolete proof experiments and
their redundant axiom-check stubs are deleted rather than
perpetuated as compatibility layers; Git history preserves
them for retrospective investigation. In-progress application
modules remain under their exact imports and are not asserted
as completed Ramsey classes.

The inventory script distinguishes actual dependencies from
an old file merely having a successful historical compilation.
Removing an abandoned file never changes the hypotheses of a
public theorem, and full CI must pass after each cleanup.

## Working manuscript

The manuscript uses reversible, explicitly approved textual
corrections and nonprinting validation/TODO overlays.
The frozen-source checker reconstructs its published historical
Git blob after reversing approved changes and stripping markers.
This guards against accidental changes to mathematical prose.
Actual TeX compilation remains a separate check from Lean CI.

## Continuing the formalization

Maintain the source API, wiki, statement crosswalk and manuscript
markers together when a **complete** new Lean proof passes CI.
Outstanding targets include the full Steiner class instance,
metric and unary-function applications, primitive-function
transfer, and separate validation of the original native proof.
A possible erratum is an author/editorial decision following
review of the revised manuscript and formal evidence.
