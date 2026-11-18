# Relative-root continuation equivalence: native functional candidate

17 November 2026. **New English theorem/proof audit only. No replacement of the frozen manuscript and no Lean certification of this theorem.** This note supersedes the one-hunk all-connected-piece equivalence as a proposed *minimal* repair. The old one-hunk patch is too restrictive in infinite signatures, and the six-cycle nonlocally finite witness example obstructs the old maximal-witness lemma.

## The proposed finite-root definition

Let `K = Forb_he(F)_fin`, where every forbidden source is finite and connected and L carries the manuscript's native (possibly partial) functions. For a finite full closed root `X in K`, write `Ext(X)` for the finite allowed structures containing X as a full substructure.

For `A, B in Ext(X)`, put

`A ~_{F,X} B iff for every C in Ext(X), [A +_X C in K iff B +_X C in K]`.

Define `I_X(A) = {C in Ext(X) : A +_X C notin K}`. Thus equivalence is equality of the `I_X` rows. The **uniform** regularity condition is

`for every n >= 1 there is k(n) such that every n-vertex X in K has at most k(n) ~_{F,X}-classes.`

This counts NEW rooted-extension information **relative to the old structure X**, rather than globally counting the infinitely many old root diagrams of an infinite language.

### The precise candidate theorem

If this uniform condition holds, then `K` has a precompact relation-only expansion by at most k(n) new n-ary predicates at each arity n, with all new predicates on pairwise distinct coordinates only. Its age has strong amalgamation with **free old-language reduct**, exact old shadows and unchanged native functions. In the finite relational case the Fraisse reduct is omega-categorical, universal for countable K and existentially complete in K. The structural proof does not require the printed tuple-surjective image-closure condition.

For arbitrary old languages, countability of the lifted age remains a separate hypothesis before invoking Fraisse, as in the manuscript. Nullary data require the usual common empty-root convention for JEP (the same issue already exists for unrestricted free amalgamation of partial nullary functions). This theorem concerns the finite age; countable non-locally-finite functional universality is NOT asserted.

This statement is *not* the unchanged original canonical minimal-cut lift. A definition of its new max-continuation lift is necessary. An isolated edit to the old `~_F` definition does not suffice while the canonical relation test insists on distinct source-root images.

## Sufficient condition: proof via maximal finite continuations

(1) **Free versus arbitrary amalgam.** If A,C have any allowed full amalgam over X, the native free amalgam A+_X C has an EHN map into it: every full irreducible test is contained in a side. Consequently the free amalgam is allowed. This is the existing native functional fold theorem, not an assertion about arbitrary image substructures.

(2) **Self compatibility.** The folding EHN map `A+_X A -> A` shows `A notin I_X(A)`. Any full extension A<=B yields `I_X(A) subset I_X(B)`.

(3) **Finite maximal witnesses.** For fixed finite X and finite A>=X, only finitely many I_X-types are reachable from A by finite full allowed extensions. Choose W>=A of maximal reachable I_X-type. Its type cannot increase in any further finite allowed full extension. Such W is *maximal on X*.

(4) **Restriction.** If Y<=X<=W are closed finite substructures and W maximal on X, then W maximal on Y. Indeed, if an allowed extension of W made `W +_Y C` newly forbidden, then `X +_Y C` is an allowed extension of X whenever `W +_Y C` is allowed, and the identity
`W+_Y C = W+_X (X+_Y C)`
would increase I_X(W), contradiction. Equality of I_X also determines equality of I_Y by the same identity, treating contexts X+_Y C which are independently forbidden as automatically bad.

(5) **Coherent predicates.** For each ordered isomorphism type of a closed n-vertex old root X, choose an enumeration of its `~_{F,X}` classes by indices in `{1,...,k(n)}`, transported by order-preserving isomorphisms. For a finite A in K, choose a finite W>=A maximal on A. On an injective tuple enumerating a closed substructure Y<=A of size n, put Q_{n,i} iff the I_Y(W)-class has index i. All repeated-coordinate tuples are false. This is relation-only and respects old functions. Heredity follows from (4); exact shadows from (3). For a fixed finite A there are finitely many closed subsets and one label each, hence precompactness.

(6) **Strong free amalgamation.** Let A*,B* agree over their common closed X*. Choose finite witnesses W_A>=A and W_B>=B maximal on A and B. The index on the tuple listing X shows I_X(W_A)=I_X(W_B). Since W_B is self-compatible, W_A+_X W_B must be allowed. Its full closed old substructure on A union B is precisely the free amalgam C=A+_X B. Extend the whole allowed finite witness to W_C maximal on C. Since W_A and W_B were already maximal on A and B, respectively, all their continuation classes on closed subroots remain unchanged. The expansion induced from W_C on C is the required strong amalgam A*+_X B*, with free old reduct. Empty-root JEP follows from connected forbidden sources and compatible nullary diagrams.

(7) **Finite-relational generic conclusions.** The generic reduct is forbidden-free by the finite-source argument. Omega-categoricity follows because each n-element old graph has finitely many expansions and there are finitely many old n-element structures. Every countable K-model has an expansion with age K* by compactness of the inverse system of finite expansion fibres (any finite family of restrictions is jointly realized by a lift of their finite union), and hence embeds in the generic. For existential completeness, embed over a finite A* one of its finite maximal witnesses W_A into the generic by its extension property. A finite existential witness in any allowed extension of the generic lies with W_A in a finite old substructure C. A finite witness maximal on C retains the type of W_A on A, hence C has a lift extending A*. The generic realizes it over A, proving EC.

No image closure, native function value quotient or local-finiteness of ambient countable witnesses occurs in (1)-(6).

## Why this is not unnecessarily restrictive

**Necessity for precompact AP with exact shadows.** For any such lift K*, let E_X be the FINITE set of lifted versions of each finite root X. For A>=X let S_A be the subset of E_X consisting of root expansions extendible to some lifted A. Then

`A+_X C in K iff S_A intersection S_C != empty`.

Forward: lift the allowed free amalgam and restrict. Reverse: amalgamate the expanded sides over their common expanded root; the allowed old amalgam makes the free old amalgam allowed by the native EHN fold. Thus I_X(A) is determined by S_A and there are at most `2^{|E_X|}` continuation classes. If the new language has finitely many diagonal-free relations of each arity, |E_X| has a UNIFORM bound for |X|=n, proving the displayed uniform condition necessary for that precise form of expansion. With merely precompact (not uniform finite-per-arity) lifts, only fixed-X finite index is forced.

## Finite family in an arbitrary old functional language

This is the strongest check of the earlier CSS objection.

For every original `S in F`, every closed proper separator `R<=S` with at least two components outside R, and every component C of S\\R, take the rooted SOURCE pattern `S[R union C]` enumerated on ALL of R. On an n-vertex root X, a query consists of such a pattern and an arbitrary root assignment R->X; coordinates may repeat. There are at most

`T_F(n) = sum_{S in F} sum_{closed separating R<=S} #Comp(S\\R) * |R|! * n^|R|`

queries. The number is finite for finite F even in an infinite relational/functional language, and irreducible forbidden sources contribute ZERO terms.

If two allowed extensions A,B>=X agree on these finitely many source-pattern realizations, then for every allowed C>=X the forbidden maps into A+_X C and B+_X C are equivalent. Given an original source map f:S->A+_X C, the pullback R=f^-1(X) is function-closed. Components of S\\R lie on just one target side. For each A-side component, the restriction to `S[R union component]` is an EHN map into A, hence can be transferred to B on the same (possibly repeated) target root values. Gluing the maps across the ORIGINAL source preserves every irreducible closed source test, so produces an EHN map S->B+_X C. The reverse follows symmetrically. No source image is forced to be function-closed.

Therefore `|Ext(X)/~_{F,X}| <= 2^{T_F(n)}` UNIFORMLY. This proves the finite-forbidden functional case directly, without semantically closing F or enumerating infinite target images.

More generally, if F=F_irr union F_fin, where all F_irr are irreducible and F_fin finite, only the F_fin sources contribute crossing patterns. The same bound applies. This is the correct conditional interface for the CSS application's printed "irreducible family plus finite family" reduction. It DOES NOT independently validate its printed assertion that its second family is finite in the infinite language or the subsequent local-completion/Ramsey step.

## Adversarial boundaries

* The old revised-equivalence-on-ALL-connected-pieces criterion is strictly TOO STRONG in an infinite old language, including the finite F={C3,C5} unary-labelled width-three example and the all-arity functional variant.
* Finite continuation equivalence is necessary for precompact amalgamation; the uniform version matches the desired diagonal-free finitely-many-new-relations-per-arity format. Thus no artificial old-root-label inflation remains.
* The old definition of maximal F-lifts permits countable non-locally-finite witnesses; the six-cycle/function-chain example remains a counterexample to its original *particular* lift. Our candidate constructs finite witnesses maximal with respect to finite allowed continuations; it does not claim that simply replacing old piece equivalence makes the old canonical lift valid.
* The claim of an **unconditional** AP lift for arbitrary F without uniform regularity is a separate raw-source-trace construction. English analysis is in PR #1263. The finite-index theorem above is not itself an unconditional replacement of the first clause of the printed theorem.
* The published complement-regularity lemma cannot simply be reused with the changed equivalence. The classification equivalence and Ramsey Theorem 3.23 need their own proof updates.
* If the original language permits truly nullary functions, compatibility of the empty-root diagrams is essential to JEP even for F empty. Do not silently claim general JEP without it.
* This is a new proof at the finite-age theorem scope; no Lean kernel endpoint proves the entire result. The CI-verified Lemma in PR #1279 covers only persistence of forbidden contexts.

## Lean re-verification contracts

RCR-01: native free-to-full EHN fold and self-compatibility (existing kernel, check exact hypotheses).

RCR-02: continuation incompatibility upward monotonicity and exact equivalence on fixed closed root (new).

RCR-03: finite-index maximal-witness selection, including closed subroot restriction (new).

RCR-04: uniform per-arity type-indexing over arbitrary old root isomorphism types (new).

RCR-05: strong AP with free old reduct for the new continuation expansion (new).

RCR-06: finite forbidden source cut-pattern transfer with collapsed roots and arbitrary native functions (new; related conditional component lemmas in PR #1263).

RCR-07: irreducible-family locality, finite F_irr union F_fin interface for the CSS application (new).

RCR-08: necessity of fixed-X finite continuation index from ANY precompact exact-shadow AP lift (new).

RCR-09: finite-relational countable generic universality / existential completeness (new).

RCR-10: classification theorem and Ramsey transfer statements (separate pending audits).

Status: English proof candidate, awaiting independent referee/Lean. Frozen manuscript unchanged.
