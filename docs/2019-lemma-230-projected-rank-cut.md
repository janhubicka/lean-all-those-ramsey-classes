# 2019 Lemma 2.30: exact higher-rank Picture obligation

11 October 2026 — proof-obligation audit, **not** a proof of Lemma 2.30.

This document follows the mathematical statements and notation of the
2019 *All those Ramsey classes* paper, particularly the proof of
Lemma 2.30 (the `j` to `j+1` step). The published source remains
frozen. Our proposed *coordinated* correction changes the Definition
2.15 **map** to protect exactly U-closed U-irreducible induced
substructures, and the Definition 2.17(4b) tests to those same closed
irreducibles. Intrinsic U-irreducibility is otherwise unchanged. Clause
(4c) continues to quantify over **all exact weak n-vertex tests**.

## What the published induction needs

Fix finite closed A,B in K, a closed finite control C0 with
`C0 -> (B)^A_2`, and j >= 0. Assume that every *closed* induced
substructure of C0 of U-size <= j admits a (K,U)-completion, using the
coordinated map. The desired C must simultaneously have:

1. A U-closed relational carrier and a positive protected projection
   `p:C -> C0`;
2. `C -> (B)^A_2`;
3. K-completions of every U-closed induced substructure of C of U-size
   <= j+1, with enough map functoriality to restrict to weak sources;
4. K-membership (or K-copy coverage) for each **closed** U-irreducible
   induced substructure.

The printed proof maintains these across intermediate pictures
`P_0,...,P_b`, using an initial disjoint union of B-copies, native
Hales–Jewett refinements and multiple free attachments. Merely proving
(1), (2) and (4) does not imply (3).

## Exact mixed-cut case

Take a hypothetical closed counterexample F of U-size <= j+1 in the
next picture. It can be necessary to split F as a free amalgam

    F = F_left ⊕_Q F_right

where Q is a closed source separator. Let the composite source
projection be `p:F -> C0`. In order to apply the existing *checked*
projected completion theorem, one needs all of the following together:

- the source free-amalgam diagram, with semi-closed sides and closed
  common Q, including genuine full side embeddings;
- a single protected positive map p (not independent maps on sides);
- an embedded closed A-copy in C0 that contains **every** p-image
  of the source separator Q, so its closed image hull belongs to K;
- two finite sets JL, JR **in the projected control C0** whose
  cardinalities are both <= j, and whose respective U-closure hulls
  contain the **entire projected left and right side images**;
- prior-stage K-completions of the two closed projected hulls,
  obtained from their absolute U-size bounds, plus strong amalgamation
  over the **same** closed K-boundary.

The last three requirements are not implied by the bare existence of
a free cut. In particular, the strict rank drop in the 2019 proof
must be established for the *projected absolute supports*, not only
for generator sets relative to the common Q.

## Exactly what partite-construction already certifies

At the dependency revision pinned in lakefile.toml:

- `ClosureRelativeGeneratorDrop.lean` gives strict **relative**
  generator support drop on each source side, with all of Q supplied
  at no cost. It explicitly does not assert smaller *absolute* U-size.
- `ClosureProjectedRankGlue.lean`,
  `HasClosedUKCompletion.of_common_projection_supports` and
  `...of_common_projection_generators`, glue two projected
  rank-j K-completions over the same K-member when the **absolute
  projected support budgets** and separator-in-A-copy hypotheses are
  already provided.
- `ClosureRelativeMapGlue.lean` gives positive gluing on arbitrary
  weak source restrictions while protecting embedded closed tests.
  The source separator need not be closed in this latter result, but
  the common TARGET boundary must still be a closed K-member.
- `ClosureClosedCompletionRank.lean`,
  `HasClosedUKCompletion.of_closed_USize`, converts a proved
  closed U-size rank invariant to completion of an *exact* weak
  source by restricting the completion of its ambient generated hull.
  It does not construct the rank invariant.

These results are useful reusable ingredients, not replacements for
the published Lemma 2.30 proof or its missing Picture geometry.

## Candidate rank-increment trichotomy to prove

For **every** closed F of U-size <= j+1 in a newly attached picture,
prove at least one of the following, with the original carrier and
the concrete attachment maps recorded:

**(I) Small projected rank:** the U-closed hull of p(F) inside C0
has U-size <= j. Apply the prior rank-j completion there and pull back
the protected positive map.

**(II) One old copy / core:** F embeds fully into an already verified
old picture or into a controlled closed core, and its rank-(j+1)
completion certificate transports along that embedding.

**(III) Certified mixed cut:** F has the free diagram and all absolute
projected-support and common-A-boundary certificates stated above;
then apply `HasClosedUKCompletion.of_common_projection_generators`
and strong amalgamation.

The 2019 prose suggests a cut by one old copy and a strict generator
drop, but has not supplied a Lean proof of this **entire trichotomy**,
especially the (III) budgets. Proving only a relative generator drop
is insufficient. Also beware a projected image p(F) may be a weak
nonclosed induced test: take its closure **inside C0 for rank control**,
never redefine the (4c) tested source as that hull.

## Separate final step, Lemma 2.31

After constructing the rank-n witness C, one must prove that **every
induced vertex set S of cardinality <= n**, including nonclosed S,
has the coordinated K-completion. The source of its completion must
remain C|S, not C|cl_C(S). The conditional bridge is recorded in
`InducedClosed2019WeakRankBridge.lean` (PR #99); it uses the already
checked `HasClosedUKCompletion.of_closed_USize` and the one-way
embedded-to-induced completion-map implication.

## Remaining tasks (precise)

1. Formalize the native Picture history and attachment provenance
   so every closed counterexample falls under I, II or III.
2. Establish both **projected absolute support** budgets in III from
   actual Hales–Jewett-based Picture geometry, or replace III with a
   provably sufficient simultaneous relative-completion invariant.
3. Verify that the map and closed-irreducible coverage invariants
   survive all intermediate stages, including the unrestricted
   semi-closed recursive stage of the printed Lemma 2.28.
4. Keep the quantifier order: n(B,C0) fixed *before* building C.
5. Separately reconcile abstract embedded-test APIs with the paper's
   induced substructures; raw `StructureClass` predicates do not
   enforce isomorphism invariance.

Do not mark Lemmas 2.28, 2.30, 2.31 or general Theorem 2.18 green
until their literal repaired conclusions have immutable-commit
Lean builds, permitted-axiom audits and no unproved constructor
hypothesis. The original printed Lemma 2.29 and Theorem 2.18 remain
formally refuted under their uncorrected definitions.
