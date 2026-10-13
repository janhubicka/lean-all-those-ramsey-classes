# Lean formalization of *All those Ramsey classes* (2019)

Jan Hubička and Jaroslav Nešetřil, *All those Ramsey classes (Ramsey classes
with closures and forbidden homomorphisms)*, **Advances in Mathematics**
356 (2019), 106791. DOI: https://doi.org/10.1016/j.aim.2019.106791

## Current verdict — 13 October 2026

**The unrestricted coordinated repair of Theorem 2.18 is not yet proved.**
There is **one remaining construction obligation**, not two: the general
`j >= 1` to `j+1` closed generating-rank Picture increment of Lemma 2.30.
The unrestricted initial Picture of corrected Lemma 2.28 is already
constructed, including a possibly nonclosed original Ramsey control.

The current general-theorem interface is
`coordinated2019_ramsey_of_higher_rank_constructor` in
`AllThoseRamseyClasses/Published/InducedClosed2019UnrestrictedInitial.lean`.
Its higher-rank constructor is an explicit premise, not a proved theorem.
The older two-constructor interface records an earlier proof state.

See **[the current status and detailed direct two-vertex proof](docs/current-main-theorem-status.md)**
for the reviewed PRs, verification evidence, new cutoff-two development,
and the exact remaining implication. `docs/validation-status.md` and dated
notes retain the longer historical coverage record.

## Scope and editorial policy

We distinguish the literal **published 2019 definitions** from the
explicitly coordinated corrected definitions. This is not a silent
substitution of the later survey's set-valued-function or total-fibre
conventions. Both the literal counterexamples and the corrected interfaces
are retained and audited.

The separate manuscript is in
[janhubicka/All-those-Ramsey-classes](https://github.com/janhubicka/All-those-Ramsey-classes).
After the author's 13 October authorization, its **working edition** applies
the coordinated two-definition repair and settled corrections. There are
31 reversible edits in its correction manifests. The published source
remains recoverable by the manuscript's reconstruction audit. Older notes
saying that no working prose may change are historical policy, not the
current authorization. Do not make additional editorial decisions or mark
an unresolved main theorem as validated.

We reuse
[janhubicka/partite-construction](https://github.com/janhubicka/partite-construction)
as a pinned Lake dependency. The initial targets are Definitions 2.12–2.17,
Lemmas 2.23–2.31, and Theorems 2.18 and 2.19.

## Critical semantic distinctions

The literal Definition 2.15 protects **all intrinsically U-irreducible
induced tests**, including nonclosed ones. The literal Theorem 2.18 and
the one-clause-(4b)-only repair have checked counterexamples; see
`docs/literal-counterexample.md` and the corresponding formal modules.

The coordinated repair changes BOTH the protected map tests in Definition
2.15 and the membership tests in Definition 2.17(4b) to tests which are
**intrinsically U-closed and U-irreducible**. Intrinsic irreducibility itself
is unchanged. Clause (4c) still concerns **every original exact weak
induced vertex set** of size at most the fixed cutoff n(B,C0). No weak test
is silently replaced with its closure.

A bound on vertex cardinality is not a bound on the cardinality of a
closed hull with small generating U-size. Completing a weak generating
set does not extend its chosen completion to a prescribed ambient hull.
The current cutoff-two result must not be substituted for the missing
general closed rank-one-to-rank-two increment.

## Validation legend

- **Green / `\\leanverified`**: the exact cited statement is proved at a
  recorded commit with successful build and permitted-axiom audit. A
  corrected statement is explicitly identified as corrected.
- **Orange / `\\leanpartial`**: a checked component or conditional theorem;
  the broader manuscript assertion still has obligations.
- **Blue / `\\leaninterface`**: representation or encoding, not proof of
  the associated mathematical assertion.
- **TODO**: correction, counterexample, or unproved step; historical
  proposals and applied working-edition corrections are distinguished.

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
No `sorry` or additional axioms are accepted in green results. A green
conditional theorem does not certify its unproved constructor premises.

## Build and contribution layout

The toolchain and GitHub Actions setup follow the pinned
`partite-construction` dependency. `lake build` builds the library;
`lake env lean CheckAxioms.lean` checks the main wrapper audit.

CI discovers every Lean file under `AllThoseRamseyClasses/` and builds
every module. It also discovers every `CheckAxioms*.lean` and checks all
listed declarations against the three permitted logical axioms. New
results remain unverified until their actual CI build and audit succeed.

A new verification module can therefore add its own namespaced source
and uniquely named `CheckAxiomsSubject.lean`, without repeatedly editing
the umbrella import or shared audit file. Consolidate public imports
when the feature is complete, rather than creating avoidable parallel-PR
conflicts.
