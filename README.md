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

## Corrected 2019 proof coverage (12 October 2026)

The *literal* published Theorem 2.18 and the one-clause (4b)-only
replacement have formal counterexamples. The preferred **coordinated
repair** changes the protected map tests in Definition 2.15 and the
membership tests in Definition 2.17(4b) to precisely those induced
substructures which are both intrinsically U-closed and U-irreducible.
All exact nonclosed small tests in Definition 2.17(4c) remain. We do
**not** claim the unrestricted corrected Theorem 2.18 has been proved.

The individually CI-green and axiom-audited components now include:

- The corrected **Lemma 2.29** with the printed relative-A-copy
  hypothesis, and the actual **Lemma 2.30 j=0** Hales–Jewett Picture
  constructor, rather than an assumed Ramsey witness (PRs #98, #106).
- Exact induced/embedded closed-test map, K-completion and
  multiamalgamation-class equivalences under explicit class
  isomorphism invariance (PRs #101, #103, #104, #107).
- Native finite Picture **rank-j preservation**, plus completion
  whenever projected generating support has size <=j, including
  the generator-collision branch and the sharp maximal-rank
  alternative (PRs #109, #111, #112, #117).
- Genuine native Hales–Jewett local common-coordinate and
  zero/one generator-active line completions, and exact factorization
  of rank-r tests through subattachments with at most r private
  copy indices (PRs #113, #115, #116).
- Corrected mixed-cut strong-amalgamation completion **provided**
  the source free split, common K-boundary and both absolute
  projected rank-j support bounds are supplied (PR #114).
- Finite heterogeneous iteration from a constructed rank-one
  base to all exact weak n-vertex completions, and the final
  Theorem 2.18 implication from two explicitly named constructor
  hypotheses (PRs #99, #108, #110).
- The generally valid weak ambient-hull rank inequality
  USize(cl_B(B0)) <= USize(B0), correcting a false equality
  printed after Definition 2.25 (PR #105).

**Remaining main construction obligations:** the unrestricted
initial closed Picture over a possibly nonclosed Ramsey control
(published Lemma 2.28) and the **j>=1 to j+1** native Picture
rank increment (Lemma 2.30), especially maximal projected-rank
sources meeting multiple transverse Hales–Jewett lines. A free cut
does not automatically give small absolute projected side ranks,
nor does completing a weak generating set complete its prescribed
closed hull. The original article stays frozen; the exact
correction proposals and validation markers are in its separate
TeX repository.

## Build

The initial setup uses the same Lean toolchain and GitHub Actions approach as
`partite-construction`, with the latter pinned to a reviewed commit.
`lake build` builds the library, and `lake env lean CheckAxioms.lean`
checks the published-statement wrappers for permitted axioms.

Until a new CI run succeeds, all new declarations are **unverified**; existing
upstream proofs retain only their own upstream CI status.

## Adding verification modules without conflicting imports

CI discovers every Lean file in `AllThoseRamseyClasses/` and builds each
module. It also discovers every `CheckAxioms*.lean` and checks all listed
declarations against the same three permitted logical axioms.

A PR proving a new fact can therefore add a single namespaced source
file and a uniquely named `CheckAxiomsSubject.lean` without editing
`AllThoseRamseyClasses.lean` or the shared `CheckAxioms.lean` every time.
The umbrella module remains a convenient stable import for reusable
verified theorems; update it when consolidating a feature, rather than
causing avoidable conflicts in every parallel audit PR.
