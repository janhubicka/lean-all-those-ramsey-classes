# Library audit: statement fidelity, trust and dead-code policy

The project certifies two distinct things: (1) Lean's kernel checks
the elaborated statements under explicitly audited assumptions;
(2) a mathematical statement audit compares them with the
published 2019 paper, recording both substantive corrections
and parts of the printed proof still unfinished.

## Adversarial audit A — mathematical quantifiers

* The literal protected map tests all intrinsic U-irreducibles,
  even those not U-closed. Paired-equivalence counterexamples
  disprove the universal theorem with that wording.
* The coordinated repair simultaneously changes the protected
  map tests and (4b) to those structures which are BOTH
  intrinsically U-closed and U-irreducible.
* Clause (4c) requires all **original exact weak induced subsets**
  S with cardinal at most the already fixed n(B,C0). Replacing S
  by its U-hull, or choosing n after seeing the weak C, is unsound.
* Original control C0 can be nonclosed; a protected map need not
  be globally injective.
* The native generating-rank proof remains unverified; the
  alternative strict-profile proof establishes the corrected
  theorem without postulating that rank-constructor.
* New class examples are not Ramsey merely because their
  strong-amalgamation sublemmas are proved. The complete
  ordered-poset instance is now checked; Steiner remains partial.

## Adversarial audit B — Lean soundness

The repository workflow builds **every** module under
`AllThoseRamseyClasses/`, not merely the curated umbrella.
It runs all `CheckAxioms*.lean` endpoints and the
`scripts/check_axioms.py` permitted-axiom audit.
Allowed axioms: `propext`, `Classical.choice` and `Quot.sound`.
The paired-equivalence, strong-amalgamation and coordinated-cycle
finite regressions are also executed.

The additional `scripts/audit_library.py` scans executable Lean
code after removing nested comments and string literals. It
rejects `sorry`, `admit` and explicit local axioms/constants,
checks missing local imports and cycles, and enforces the
application-neutral `PublicAPI`.

A successful bounded regression is not a kernel proof.
Conversely, a kernel proof of a conditional proposition P → Q
is not an unconditional proof of Q. Public status tables
record the precise final theorem scope.

## Adversarial audit C — maintainable research library

The curated umbrella imports the completed `ApplicationsAPI`,
which imports the corrected `PublicAPI` and the proved
ordered-poset theorem. Historical counterexample modules and
native Lemma 2.30 experiments are directly importable and
individually built, not silently dragged into the default API.

The source audit reports modules unreachable from the public
imports. **Import-unreachable does not prove dead:** a file may
be an axiom-check root, a published-statement counterexample
or ongoing separate formalization. Delete only after inspecting
all importing modules, `CheckAxioms*.lean` roots, manuscript
validation references, and mathematical reuse. Arbitrary
removal of historical evidence would harm reproducibility.

## Original manuscript safety

The TeX source's approved corrections are recorded in ordered,
reversible manifests. `scripts/check_frozen_annotations.py`
removes nonprinting Lean blocks, reverses approved textual
changes and compares the resulting historical Git blob; it also
checks numbered mathematical environments. Extra green/orange/blue
markers and TODOs are nonprinting in ordinary output.

The private manuscript CI failures before runner allocation do
not establish any TeX compilation error or successful TeX build.
A static environment check is not a substitute for pdflatex.

## Next verification targets

Finish strong amalgamation and exact local completion for
freely ordered partial Steiner triples; continue auditing the
original Lemma 2.30 without mixing it into the alternative
main theorem; validate remaining metric, unary, pointed,
interposition and incidence class examples; prove the separate
primitive-function formulation/transfer if desired.
Update this wiki and the annotations only after complete
Lean CI and permitted-axiom verification.
