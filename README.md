# Lean formalization of *All those Ramsey classes* (2019)

Source: Jan Hubička and Jaroslav Nešetřil, *All those Ramsey classes
(Ramsey classes with closures and forbidden homomorphisms)*,
**Advances in Mathematics** 356 (2019), 106791.
DOI: https://doi.org/10.1016/j.aim.2019.106791

## Scope and editorial policy

This repository checks the **published 2019 definitions and theorems**, not a
silent substitution of the later survey's set-valued functions or total-fibre
homomorphisms. The published paper, including its arXiv source in
[janhubicka/All-those-Ramsey-classes](https://github.com/janhubicka/All-those-Ramsey-classes),
is **frozen**. Inaccuracies and proposed exact corrections go to separate
`annotations/` and `docs/` files, never into its mathematical prose.

We reuse the formally checked relational closure and partite infrastructure
from [janhubicka/partite-construction](https://github.com/janhubicka/partite-construction)
as a pinned Lake dependency. The initial target is Definitions 2.12–2.17,
Lemmas 2.23–2.31, Theorems 2.18 and 2.19; see the coverage table in
`docs/validation-status.md`.

## Critical semantic distinction

The *literal* Definition 2.15 tests **all intrinsically
`U`-irreducible induced substructures**, even if they are not themselves
`U`-closed. In particular singletons are irreducible; the published
Definition 2.17(4b) can become vacuous whenever the target class has no
singletons. The ordered paired-equivalence/matching example supplies a
non-Ramsey class satisfying the literal conditions: see
`docs/literal-counterexample.md`.

The candidate **closed-test repair** is maintained as a different interface
from the literal printed definitions; no claim of equivalence is made.

## Validation legend (same as the survey)

- **Green / `\\leanverified`**: full published statement proved in Lean at
  a pinned commit with successful build and permitted-axiom audit.
- **Orange / `\\leanpartial`**: checked mathematical core only; broader
  published statement or proof obligations remain.
- **Blue / `\\leaninterface`**: a matching representation or encoding
  exists; not a proof of the associated statement.
- **TODO**: an inaccuracy, counterexample, or unproved proof step; precise
  proposed replacement text is recorded without changing the publication.

Use Lean's standard logical axioms only (`propext`, `Classical.choice`,
`Quot.sound`); no `sorry` or additional axioms are accepted in green results.

## Build

The initial setup uses the same Lean toolchain and GitHub Actions approach as
`partite-construction`, with the latter pinned to a reviewed commit.
`lake build` builds the library, and `lake env lean CheckAxioms.lean`
checks the published-statement wrappers for permitted axioms.

Until a new CI run succeeds, all new declarations are **unverified**; existing
upstream proofs retain only their own upstream CI status.
