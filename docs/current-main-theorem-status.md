# Current main-theorem status — 13 October 2026

This file is the current summary. `validation-status.md` and the dated native-history notes retain the detailed development history; older statements that Lemma 2.28 is still missing are superseded here.

## Verdict and corrected statement

**The unrestricted coordinated 2019 Theorem 2.18 remains open. There is ONE remaining constructor, not two.**

`InducedClosed2019UnrestrictedInitial.lean` already constructs corrected Lemma 2.28 over an arbitrary, possibly nonclosed Ramsey control (PR #121). Its theorem `coordinated2019_ramsey_of_higher_rank_constructor` reduces the main theorem to `Proposed2019RankIncrementStep` for every j >= 1. Finite iteration and the exact weak-test final transfer are proved conditionally on that constructor. The earlier two-constructor interface is historical, not the current list of obligations.

The working manuscript has already applied the coordinated Definition 2.15 / Definition 2.17(4b) change: protected map tests and K-membership tests are the induced structures that are both intrinsically U-closed and U-irreducible. Intrinsic U-irreducibility itself is unchanged. Clause (4c) still quantifies over ALL original weak induced vertex sets of size at most n(B,C0). Do not replace those tests with generating sets or hulls. The 31 authorized working-edition edits are reversible; the separate TeX repository retains the published-source reconstruction audit.

## Inherited PRs now reviewed, verified, and merged

| PR | Exact proved scope | Successful complete CI run | Merge |
| --- | --- | --- | --- |
| #185 | Two actual private-active labels imply literal REST root size + 2 <= source size. | 38457824272 | c08a2829934de690fed87d620b74a231aa8d698b |
| #186 | Closed maximal-rank source with <=3 vertices and precisely two active labels, given old closed rank two, completes over its literal K-root. | 38458189850 | be7b579ce81e89d922a19c1a86ede598b4379247 |
| #187 | Maximal weak source with <=2 vertices and precisely two active labels has an empty closed K-root; old closed rank one suffices. | 38459562397 | d1c376370f27148a6acc3db1a74a65ba4fcaa4c9 |

Each run completed the full module build, permitted-axiom audit, regressions, and admission scan. No general higher-rank claim follows from these source-cardinality special cases.

## Direct two-vertex theorem and cutoff-two endgame — verified and merged PR #188

New declarations, both in namespace `AllThoseRamseyClasses.Published`:

* `inducedClosed2019_exact_weak_card_le_two_completion` in `AllThoseRamseyClasses/Published/ExactWeakTwoVertex2019.lean`.
* `coordinated2019_cutoff_two_unrestricted_induced` in `AllThoseRamseyClasses/Published/InducedClosed2019CutoffTwo.lean`.

The first theorem removes the native active-line and external old-rank assumptions from the two-vertex completion problem entirely. The second constructs the actual K-Ramsey witness whenever the exact local-completion cutoff is <=2. It allows the original Ramsey control to be nonclosed and does not take a rank-increment constructor as a premise.

### Complete English proof of the direct theorem

Let C be a finite U-closed Picture with original closed U-irreducible B-copy coverage, B in K. Assume finite strong amalgamation, closed heredity of K, and ordinary irreducibility of K-members. Fix the ORIGINAL weak induced source F=C|S with |S|<=2.

Closed rank-one completion in C is automatic: a closed rank-one induced structure is U-irreducible, hence embeds into B by coverage.

If USize(F)<=1, its actual ambient closed hull H satisfies USize(H)<=USize(F)<=1. Thus H is closed and U-irreducible, embeds into B, and its embedding restricts to F. This is restriction of an embedding first obtained on the whole hull, NOT an arbitrary extension of a weak generating-set completion.

If F is ordinarily irreducible, its ambient hull is again closed U-irreducible and embeds into B. Restrict that embedding to F.

In the remaining case USize(F)>1 and F is ordinarily reducible. Since USize(F)<=|F|<=2, its intrinsic rank equals its vertex cardinality. Take any genuine proper free decomposition F=L amalgam_H R. Both sides have at most one vertex. The common carrier H is empty: if h were in H, every right vertex would equal its image; overlap and vertex coverage would make the left embedding surjective, contradicting properness.

Every closure rule has a nonempty root, so the exact empty H is U-closed. It is ordinarily irreducible. Its ACTUAL embedding into C gives, by B-coverage, a full embedding into B; closed heredity yields H in K. This explicitly respects nullary relational data. An arbitrary empty function is not being falsely declared a full embedding.

Both source sides have their actual full embeddings into C. They each have at most one vertex, so the old closed rank-one invariant applies after the checked image/hull construction. The common boundary is the same literal closed K-member H. Apply the audited `inducedClosed2019_maximal_weak_two_old_maps_glue_of_closed_K_root`, with Old=C and rank=1. It completes the original F. This exhausts all cases.

### Complete endgame at n <= 2

Use the already constructed unrestricted Lemma 2.28 to obtain a closed Ramsey Picture C over the original control C0, with protected projection and closed-irreducible B-copy coverage. The direct theorem completes every original weak test on at most n<=2 vertices. Closed heredity supplies the exact K-membership clause. Invoke the fixed-cutoff local completion hypothesis on C, then the checked B-copywise Ramsey transfer. The target is a finite member of K with the required Ramsey arrow.

### Validation record

PR #188 proof head: `f0395a205022a145f2f84efbc7bea6740039d03b`.
Successful complete GitHub Actions run: `38461482875`, job `115517483846`.
The full module build, permitted-axiom audit, finite regressions, and admission scan all passed. Both new declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. The logs report no unsupported axioms and no admissions.

PR #188 was squash-merged as `e8684e297974b0bfc0f63920892ccaf8c6a93f2d`, confirmed from its live PR metadata. This corrects the previous erroneous merge identifier; the proof head and CI certificate are unchanged. These exact restricted declarations are verified; the unrestricted main theorem is not. Verification was performed by GitHub Actions, not by a local Lean installation.

## General projected-boundary saturation — PR #190

See `docs/projected-boundary-saturation-20261013.md` for the complete English proof and precise Lean declarations. For a genuine free source cover S,T and a common corrected protected projection p to a closed D, assume the projected original separator lies inside one specified closed K-copy. Let H be its closure in D. Enlarging S and T by p^-1(H) makes both source sides relatively closed without changing either ORIGINAL projected closure hull. Independent completions of those hulls then glue over the actual closed target K-member D|H.

The source, original sides and original separator need not be intrinsically closed or semiclosed; maximum source rank and injectivity of p are not required. The rank-j corollary still needs BOTH original projected side-hull ranks <=j. The initial CI failure was a missing-import failure, not a counterexample; full verification of the corrected proof head is tracked on PR #190. No new green status is inferred from this note.

## Exact unresolved implication

For every j>=1, the actual `Proposed2019RankIncrementStep` must turn a finite closed control D with its Ramsey arrow, corrected closed-irreducible coverage, and completions of all CLOSED induced tests of GENERATING rank <=j into a new finite closed Ramsey Picture over D with the same properties at rank j+1.

The missing native argument must construct a true free source split, an appropriate protected projection or compatible side maps, a common closed target K-boundary, and BOTH absolute projected rank-j bounds. A separator contributes to these bounds and cannot simply be discarded. Under the common-projection hypotheses of PR #190, intrinsic closedness of the ORIGINAL source separator is no longer a necessary gluing hypothesis; source-side saturation does not increase either original projected hull.

The Boolean core-crossing counterexample rules out the claim that two transverse Hales--Jewett COPY ranges automatically form a free relational cover. Complementary RESTS give a real cover in the checked cases, but a possibly noninjective protected completion of a core root in A is still not a pair of compatible full embedded boundaries. PR #190 instead fixes an actual closed target boundary, under its explicit common-projection and separator-containment hypotheses.

**Cardinality cutoff two is not generating rank two.** A rank-two closed hull can have more than two vertices. The cutoff-two theorem therefore does not supply even the general closed rank-one-to-rank-two constructor. No full Lemma 2.30 or unrestricted Theorem 2.18 marker may be promoted on this basis.
