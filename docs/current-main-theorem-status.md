# Current main-theorem status — 13 October 2026

This is the current summary. The dated validation ledger and older native-history notes remain the historical record. The unrestricted initial Picture is no longer missing.

## Verdict and exact semantics

**The unrestricted coordinated 2019 Theorem 2.18 is not yet fully formalized.** The original construction route has one missing general constructor: `Proposed2019RankIncrementStep` for every j>=1. A new profile / relational-sparsening route is developed in `docs/profile-sparsening-route-20261013.md`; its formalization is incomplete and is not an implicit replacement theorem.

Corrected Lemma 2.28 is constructed in `InducedClosed2019UnrestrictedInitial.lean`, including a possibly nonclosed original Ramsey control. The theorem `coordinated2019_ramsey_of_higher_rank_constructor` proves the final implication from the remaining rank increment. Finite iteration and exact weak-test transfer are checked at that conditional scope.

The coordinated repair of Definitions 2.15 and 2.17(4b) is applied to the working manuscript: protected maps and K-membership test precisely the induced structures that are both intrinsically U-closed and U-irreducible. Intrinsic irreducibility itself is unchanged. Clause (4c) still quantifies over EVERY original weak induced vertex set of size at most n(B,C0). The original control and cutoff must be fixed before constructing the candidate. The 31 authorized mathematical/mechanical working-edition changes remain reversible in the TeX repository.

## Verified additions in this continuation

### PR #190: boundary saturation, with no added projected rank

For a genuine free source cover S,T and a positive map p into D, let H be a relatively closed target boundary containing p(S intersect T). The saturated source pieces

    S' = S union p^-1(H),      T' = T union p^-1(H)

are relatively closed and form a free cover of the SAME original source. When H is contained in each original projected side hull, saturation leaves BOTH projected hulls exactly unchanged.

The completion theorem glues the independently completed target pieces over the actual closed K-member D|H. It no longer requires intrinsic closedness or semiclosedness of the source, original sides, or original separator. It does not require source maximum rank or injectivity of p. The rank corollary still explicitly requires the two ORIGINAL absolute projected rank bounds; it does not claim these bounds follow from arbitrary properness.

The unbounded corollary `inducedClosed2019_weak_two_irreducible_cover_completion` completes any weak source fully embedded in a closed B-covered ambient when it is a genuine free union of two ordinary irreducible pieces. There is no cardinal or generating-rank bound, and their intersection can be nonclosed and reducible.

Seven audited declarations; proof head `3644bf01a1719f76be2feb808fef4808b428a880`; successful complete Lean CI `38470928703`, job `115549529914`; merged as `e1c4f95d9ffd6e52253289ac5bc7b22083da9f07`.

### PR #191: ALL exact weak three-vertex tests and the actual cutoff-three endpoint

`inducedClosed2019_exact_weak_card_le_three_completion` completes every original weak induced set of at most THREE vertices in a finite U-closed B-covered Picture. Assumptions are finite strong K-amalgamation, closed heredity, B in K, and ordinary irreducibility of K-members. No native-line, source-closedness, maximal-rank, or additional old-rank hypothesis occurs.

Complete proof: ordinary irreducible sources complete through their actual closed hull and B-coverage. A reducible source on at most three vertices either has an isolated vertex or is a three-vertex path in its tuple adjacency. In the first case, a genuine disjoint free cover has sides of at most two vertices; the verified two-vertex theorem completes them, and the exact empty root is closed and in K by actual B-coverage, including nullary data. In the second case, the two edge pieces are ordinary irreducible and freely cover the original source, so PR190's unbounded two-piece theorem completes it. The formal geometric dichotomy is proved directly on ALL relation tuples and allows arbitrary relational arities, repeated tuple entries, and nullary symbols.

`coordinated2019_cutoff_three_unrestricted_induced` constructs the actual finite K-Ramsey target whenever the genuine fixed local cutoff n(B,C0)<=3. It uses the unrestricted initial Picture, ALL required exact weak completions, the original local axiom, and B-copywise Ramsey transfer. It does not assume any missing rank constructor, and C0 may be nonclosed.

Eight audited declarations; proof head `1d89a1a42775e81a6b9c8ca94b828b9d0fa4f6d5`; successful complete Lean CI `38472155600`, job `115554084651`; merged as `2a63fb9c89805614fafe83f08103861761b90cf2`. The consolidated main commit adds only the four new three-vertex files (444 lines), not duplicate saturation files.

**Cardinality cutoff three is NOT generating rank three.** A closed hull generated by two or three vertices can be much larger. These results do not prove the general closed rank-one-to-rank-two increment.

## Closure records for the alternative route — PR #192

The new expansion records an actual closed induced H of fixed Base and a tuple generating H. A record is true precisely when a FULL embedding of H extends the displayed tuple. Full embeddings between closed structures preserve and reflect records: the realized H is forced into the relatively closed source image by its generators, then factors fully through that image.

The implementation also constructs an actual common closed K-boundary from ANY finite weak overlap embedded fully into two matching canonical profile expansions, and proves that the profiled finite closed Base is hereditarily ordinarily irreducible. These are statements about the NEW expansion, not claims that all unexpanded native overlaps have compatible boundaries.

Nine declarations have axiom checks in PR #192. The final source head is `356def3e6e840b857b01e805e651825c169d66f3`; its CI is pending at the time of this entry. The remaining alternate-route bridges are: strict-tree completion into canonical K-expansions; generic fresh-symbol closure tagging; transfer of BOTH tag normality and original root validity; final closed sparse witness and exact weak-test/control-map transfer. The detailed English construction records every step and the pitfalls.

## Earlier verified checkpoints

| PR | Exact scope | Successful CI | Merge |
| --- | --- | --- | --- |
| #185 | Literal two-REST root cardinality +2 <= source cardinality. | 38457824272 | c08a2829934de690fed87d620b74a231aa8d698b |
| #186 | Closed maximal source <=3 vertices, exactly two active labels, old closed rank two. | 38458189850 | be7b579ce81e89d922a19c1a86ede598b4379247 |
| #187 | Maximal weak source <=2 vertices, exactly two active labels, empty root, old rank one. | 38459562397 | d1c376370f27148a6acc3db1a74a65ba4fcaa4c9 |
| #188 | ALL exact weak <=2 tests and actual Ramsey endpoint for n<=2. | 38461482875 | e8684e297974b0bfc0f63920892ccaf8c6a93f2d |

**Provenance correction:** an earlier version of this note and the TeX addendum incorrectly recorded `daec134f9400f8816e4d89b07f7327074cd24d52` for PR188. The live merged PR metadata confirms the correct squash commit is `e8684e297974b0bfc0f63920892ccaf8c6a93f2d`. The previously pinned proof head `f0395a205022a145f2f84efbc7bea6740039d03b` and successful CI run `38461482875` were already correct; the proof content and certificate scope are unchanged.

## Remaining original-construction obligation

The native j->j+1 argument must construct a new finite closed Ramsey Picture over the previous control, with the SAME protected-map and closed-irreducible coverage requirements, and completions of all CLOSED tests of GENERATING rank <=j+1.

Boundary saturation removes source-side closedness assumptions when one common protected projection and a suitable closed K-boundary are available. It does not construct that common projection for arbitrary native histories or prove either absolute projected side-rank budget. The core-crossing counterexample still rules out inferring a free cover from two transverse Hales--Jewett copy ranges. The general theorem and native Lemma 2.30 remain partial.

All claimed verification in this ledger was performed by GitHub Actions. No local Lean build is claimed. Only the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound` are permitted; the original theorem must never be marked green merely because a conditional implication has a green audit.
