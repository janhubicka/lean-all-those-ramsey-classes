# Additional adversarial validation review — 15 October 2026

This is a **fresh, separately scoped adversarial inspection** of the maintained
formalization after merged cleanup [PR #233](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/233).
It comprises three independent *review criteria* applied to the source and
existing machine checks; it is **not** a claim of three external human referees.
The baseline full build is [Actions 38649784797](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38649784797),
commit `99d9c3eb3f3fdf409106c1e096627def652ad41f`, subsequently merged
as `c046ee48832647325ca30086180339b2f20e3e0c`.

## Reviewer A — hostile statement/quantifier comparison

The theorem exposed by `PublicAPI` is a proved
`Coordinated2019Theorem218Target`, with inputs `R`, `K`, closure rules,
ambient finite Ramsey and ordinary irreducibility hypotheses, and the
*coordinated revised* multiamalgamation class, including explicit
isomorphism invariance. It does **not** accept a rank-increment
construction, a sparse-witness oracle, or an abstract general Ramsey
theorem as an additional argument.

Critical exactness tests against
`Published/InducedClosed2019MainContract.lean`,
`InducedClosed2019TestNormalization.lean` and
`InducedClosed2019ClassBridge.lean`:

- The map clause of the revised Definition 2.15 and membership clause
  2.17(4b) both protect induced tests that are **intrinsically closed and
  intrinsically irreducible**. Requiring merely one of these would change
  the theorem.
- The local axiom (4c) selects `n` **after** the original `B,C0` but
  **before** the constructed candidate, and quantifies over **every exact
  original weak induced subset** of size at most `n`. Nonclosed subsets
  are included. Replacing `S` by its closure is **not** a legitimate
  inference.
- The original ambient Ramsey control need not be closed. Protected maps
  need not be globally injective. They must preserve **full** embeddings
  on the relevant exact tests.
- The local completion needs to preserve copies of `B` and the final
  arrow, not every unrelated copy of `A`.
- The isomorphism-invariance hypothesis is explicit because the Lean
  `StructureClass` type, by itself, does not imply it.

The equivalence `inducedClosedMap_iff_abstract_2019` uses **surjective
full embeddings onto exact induced ranges**, not a generated closure;
`inducedClosedMap_comp_2019` composes the normalized protected maps.
The iff for the local axiom separately requires the K-isomorphism
hypothesis. The conditional bridge must not be mistaken for the
unconditional main proof.

**Disposition:** no statement-level mismatch was found in the revised
relational theorem on this pass. That is a bounded source review, not
an assertion about the untouched published wording.

## Reviewer B — adversarial proof/dependency reconstruction

The verified source is
`Published/Coordinated2019ProfileSparseWitness.lean`.
We checked the following potentially dangerous implications against
the code, not just against the English description:

1. `closed_ramsey_unrestricted` first produces a closed initial Picture
   over the **unmodified** `C0`.
2. Generated-closure profile expansion preserves the Ramsey arrow and
   supplies the full expanded roots needed by
   `sparseningRamsey_strict_baseIrreducible_all`. Its `n` is the **same
   preselected** cutoff.
3. The second, fresh root-tagged Picture makes the **original reduct**
   closed and proves closed-irreducible copy coverage; auxiliary tags are
   forgotten only after these properties are obtained.
4. For a weak original `S : Finset VQ`, the proof forms
   `T := S.image Q.part` and proves `T.card ≤ n`. The small tree
   completion is pulled back along the **actual map from S to T**. There
   is no illicit extension of an `S`-completion to its potentially
   much larger prescribed closed hull.
5. It obtains an actual finite `K`-completion `E`, then upgrades the
   ordinary map on **`Qold.induce S`** to the revised protected map
   using closed-irreducible copy coverage.
6. The final protected projection is composed back to `C0`; the
   fixed-cutoff local axiom gives the B-copywise transfer and the
   unconditional `FiniteRamseyClass K`.

Special attention was paid to the otherwise easy-to-confuse
`ClosedUIrreduciblesIn` versus `CorrectedUIrreduciblesIn`
interface. The used transfers are explicit. The actual strong
amalgamation assumption remains a class field, never a fabricated
result for a concrete application.

**Disposition:** the construction closes the **revised relational**
main theorem by the profile/sparsening route. It does **not**
prove native generating-rank Lemma 2.30 or automatically give a
primitive-function statement. Those remain distinct tasks.

## Reviewer C — kernel, surface API and maintainability

On the baseline commit, CI built all **77** retained Lean library/source
modules, rejected missing imports, cycles and local admissions, and
checked **199 distinct declarations** against only `propext`,
`Classical.choice`, and `Quot.sound`.
The theorem's result type and its unconditional wrapper were also
read directly from `PublicAPI.lean`.

The extra cleanup changes the **audit layout only**:
59 tiny `CheckAxioms*.lean` files become **seven** grouped certificates.
Every old `#print axioms` command is preserved verbatim, with a
per-source provenance comment, and the public `#check` inventory
remains intact. The Python checker now verifies **multiplicity** of
each report, rather than just presence of each declaration, and
protects the 199-distinct-declaration reference floor.
Historical source comments that still called the completed alternative
proof “open” have been corrected, without modifying theorem statements.

Some imports in `PublicAPI` and `ApplicationsAPI` are transitively
redundant today, but **are deliberately retained** as explicit stable
API re-exports: their removal would save no maintained proof and would
make downstream imports depend on unrelated changes to application
internals. One genuinely redundant smoke-audit import was removed.

**Disposition:** group-file consolidation and the stricter checker
must pass their own new full CI before the cleanup is merged. Passing a
source checker is not a substitute for Lean's kernel and axiom checks.

## Explicit residual risks and next use

- The published wording and original native proof have separate
  historical status from the coordinated **revised** theorem proved here.
  This review does not give a verdict on a future erratum.
- The verified ordered-poset Ramsey class is a complete concrete
  instance. Steiner triples currently have verified ambient-Ramsey,
  strong-amalgamation components and compatible orders, **not** the
  final exact local-completion/class-Ramsey conclusion.
- Independently reused upstream `partite-construction` theorems are
  trusted through their pinned Lean dependencies and the audited
  endpoint's kernel proof; this pass did not manually referee their
  entire source line by line.
- No external independent human referee or separate parallel model
  review is claimed. The review consists of adversarial mathematical
  checks, dependency inspection, and the CI-backed integrity audit.

The next mathematical target after this cleanup is the **exact local
completion of freely ordered partial Steiner triples**, stated on the
original weak subsets. Do not publish its class Ramsey conclusion
before all class fields have been discharged in Lean.
