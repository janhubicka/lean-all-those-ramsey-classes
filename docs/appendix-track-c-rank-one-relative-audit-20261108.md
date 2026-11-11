# Appendix A / Track C: the automatic rank-one local-completion base

**Status:** PR #963 contains draft Lean proofs with six named axiom-check endpoints; CI has not yet been verified on its latest head. No changes to frozen survey TeX.

## Exact hypotheses

Let `H` be a class of genuine part-labelled partial `Option(Set)` structures, and `K(H)` its canonical old-mask/full-root-tag image. Let `C` be a tagged candidate.

We use the same premises that appear in the corrected functional Ramsey theorem:

- `IsUClosed rules C`, with `rules = (L.withParts Parts).wholeMaskClosureRules Parts`;
- corrected (4b), meaning **every induced U-closed U-irreducible test** `C.induce S` belongs to `K(H)` (not the false all-intrinsic-U-irreducible weak-test variant);
- all `K(H)` members are ordinarily irreducible. This is *derived*, not newly assumed, if `K(H) ⊆ R` and every `R` member is ordinary irreducible. It is NOT derived merely from H's hereditary property or the transversality of its output fibres.

No local-completion axiom, positive primitive function arity, strong amalgamation, fixed B-cover, global decoded class membership, or strict native B-tree is needed for this rank-one result.

## Case A: U-closed induced tests of U-size ≤1

Let `T ⊆ C` and assume `C.induce T` is U-closed and has `USize ≤ 1`. The existing checked `IsUClosed.uIrreducible_of_USize_le_one` proves U-irreducibility. Corrected (4b) therefore gives **literal membership** `C.induce T ∈ K(H)`, not merely a homomorphic image. By the ordinary-irreducibility assumption on K(H), this is an eligible completion target, and the identity full embedding is a corrected induced-closed U-homomorphism-embedding. This supplies a genuine H-relative completion with the **same carrier**.

The argument actually holds for ANY induced test that is both U-closed and U-irreducible, regardless of its rank. Rank≤1 is only one convenient sufficient criterion.

## Case B: ordinary irreducible ambient weak tests

For ANY exact subset S with `(C.induce S).Irreducible`, the already merged lemma `genuineTagged2019_correctedCovered_weakIrred_canonicalTarget` produces a **full relational embedding** of that *exact induced S* into a canonical genuine H target. The H target may be larger and depend on S. Ordinary irreducibility of all K(H) members makes it an eligible local-completion target; the full embedding automatically protects every closed U-irreducible subtest of S. In particular, all exact ambient weak tests on at most one vertex are covered, **even if they are not function-closed**, and persistent OLD domain masks are respected.

This generalizes the previous "singleton base": the only remaining new local-test work concerns **ordinary reducible** ambient weak supports.

## Consequence at local cutoff n=1

If a corrected local-completion class axiom holds with **n=1**, its all-small-tests antecedent is already true under the ambient U-closedness and corrected (4b) premises. The outer axiom therefore yields the B-copywise completion for every candidate satisfying its control premises. This does **not** assert that a locally finite class has a valid cutoff n=1. An arbitrary original cutoff n(B,C0) may be much larger.

The result is **not** the earlier fixed-point-free unary full-intrinsic-weak vacuity argument: the ambient H-relative witnesses here protect OLD domain definedness, which intrinsic full weak restriction can delete.

## Adversarial checks / unresolved extension

1. Do not confuse `C.induce S` with the canonical old-mask encoding of `wholeWeakInduce (wholeMaskOriginalDecode C) S` when S is nonclosed. Their OLD domain relations differ even if complete output tuples agree.
2. Do not infer ordinary irreducibility of a U-closure hull from U-irreducibility alone. The target is ordinary irreducible because of the **ambient irreducible class hypothesis**.
3. The empty weak test is included in `card ≤ 1`, and needs a genuine canonical H target just like a singleton. It is supplied through corrected (4b) on the U-closure hull, not by assuming a nonempty H class for free.
4. For rank≥2, a weak test may be ordinarily reducible and have parts on opposite sides of a free cut. Independent H-completions of its closed side hulls need not glue without a compatible closed common boundary. This is the higher-rank obstacle; it is not repaired by the rank-one statement.
5. No nullary-arity reduction is claimed: the proof is about existing relational U-tags and the defined H-relative completion predicate. It does not verify the separate native full-functional tree construction for nullary operations.

Source files and named axioms: `AllThoseRamseyClasses/Published/FunctionalWithParts2019RankOneRelative.lean`, `CheckAxiomsFunctionalWithParts2019RankOneRelative.lean`. CI status must be refreshed before marking any of the new theorem declarations validated.
