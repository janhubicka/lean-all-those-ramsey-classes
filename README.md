# Lean formalization of *All those Ramsey classes* (2019)

Jan Hubička and Jaroslav Nešetřil, *All those Ramsey classes (Ramsey classes
with closures and forbidden homomorphisms)*, **Advances in Mathematics**
356 (2019), 106791. DOI: https://doi.org/10.1016/j.aim.2019.106791

## Current verdict — 13 October 2026

**The unrestricted coordinated corrected RELATIONAL closure-description
Ramsey theorem is proved, CI-verified, and merged.**

```lean
import AllThoseRamseyClasses.Published.Coordinated2019ProfileSparseWitness

#check AllThoseRamseyClasses.Published.coordinated2019_profile_sparse_witness
#check AllThoseRamseyClasses.Published.coordinated2019_ramsey_by_profile_sparsening
```

The final theorem uses the established corrected multiamalgamation-class
interface, including explicit isomorphism invariance. It has **no** native
rank-increment, compatible-boundary, or sparse-witness constructor premise
and **no** restriction on the preselected local cutoff n(B,C0).

Proof PR **#195**, head `c783c23377d56d29bdfb7d61fe95e9c7e96073d2`,
passed complete GitHub Actions run **38479503776**: every project module,
the permitted-axiom audit, finite regressions, and admission scan. It was
merged as `f88ce3113076f348a06906c0e2cf6e12b47c985d`. The fresh-tag
component #194 independently passed complete run 38479196563.

The proof records generated closed boundaries, applies purely relational
strict-tree sparsening, and then uses a final closed fresh-tag Picture
pass. Both original closedness and the exact original weak-test
completions are recovered. The same original C0 and n(B,C0) are retained.

See [current status and verification certificate](docs/current-main-theorem-status.md)
and the [complete English proof and semantic audit](docs/coordinated-profile-proof-20261013.md).
Older dated status notes are historical checkpoints, not the current
verdict on this relational theorem.

**Scope boundary:** the literal published theorem remains refuted. The
old native Lemma 2.30 generating-rank argument is not proved by this
alternative route. Primitive-function formulations require their explicit
relationalization bridge; this endpoint alone does not certify that
transfer or all other numbered statements in the paper.

## Scope and editorial policy

We distinguish the literal **published 2019 definitions** from the
explicitly coordinated corrected definitions. This is not a silent
substitution of the later survey's set-valued-function or total-fibre
conventions. Both literal counterexamples and corrected interfaces are
retained and audited.

The separate manuscript is in
[janhubicka/All-those-Ramsey-classes](https://github.com/janhubicka/All-those-Ramsey-classes).
After the author's authorization, its working edition applies the
coordinated two-definition repair and settled corrections, with 31
reversible edits in the correction manifests. The published source
remains recoverable by the manuscript's reconstruction audit. The new
profile proof is supplied as a review-only addendum, not silently
substituted for the numbered original proof.

We reuse
[janhubicka/partite-construction](https://github.com/janhubicka/partite-construction)
as a pinned Lake dependency. The initial targets are Definitions 2.12–2.17,
Lemmas 2.23–2.31, and Theorems 2.18 and 2.19. Individual statement scopes
and unresolved old-proof obligations remain in the validation ledger.

## Critical semantic distinctions

The coordinated repair changes BOTH the protected map tests in Definition
2.15 and the membership tests in Definition 2.17(4b) to induced tests which
are **intrinsically U-closed and U-irreducible**. Intrinsic irreducibility
itself is unchanged. Clause (4c) still tests **every original exact weak
induced vertex set** of size at most the fixed cutoff n(B,C0). No weak test
is silently replaced with its closure.

The literal Definition 2.15 protects all intrinsically U-irreducible
induced tests, including nonclosed ones. The literal Theorem 2.18 and the
one-clause-(4b)-only repair have checked counterexamples. See
`docs/literal-counterexample.md` and the corresponding formal modules.

Completing a weak generating set does not extend its chosen completion
to a prescribed ambient hull. Cardinal cutoff two is not closed generating
rank two. The new theorem succeeds by a different construction; it does
not erase the counterexamples to shortcuts in the old rank proof.

## Validation legend

- **Green / `\\leanverified`**: the exact cited statement is proved at a
  recorded commit with successful build and permitted-axiom audit. A
  corrected statement is explicitly identified as corrected.
- **Orange / `\\leanpartial`**: a checked component or conditional theorem;
  the broader manuscript assertion or proof still has obligations.
- **Blue / `\\leaninterface`**: representation or encoding, not proof of
  the associated mathematical assertion.
- **TODO**: correction, counterexample, or unproved step; historical
  proposals and applied working-edition corrections are distinguished.

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
No `sorry` or additional axioms are accepted in green results. A green
conditional theorem does not certify its constructor premises.

## Build and contribution layout

The toolchain and GitHub Actions setup follow the pinned dependency.
`lake build` builds the default library. To check the new endpoint:

```sh
lake build AllThoseRamseyClasses.Published.Coordinated2019ProfileSparseWitness
lake env lean CheckAxiomsCoordinated2019ProfileMain.lean
```

CI discovers every Lean file under `AllThoseRamseyClasses/` and builds
every module, including those outside the convenience umbrella import.
It also discovers every `CheckAxioms*.lean` and checks all listed
declarations against the three permitted logical axioms. New results
remain unverified until their actual CI build and audit succeed.

New verification modules can add their own namespaced source and uniquely
named `CheckAxiomsSubject.lean`, avoiding unnecessary parallel edits of the
umbrella import or shared audit file. Consolidate public imports when a
feature's interface is stable.
