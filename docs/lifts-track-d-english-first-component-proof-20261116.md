# Track D: English-first source-preserving proof at unrestricted native scope

16 November 2026. This continuation follows the user's explicit order: detailed English proof, adversarial audit, then validation. **No new Lean declarations are included.** The frozen numbered manuscript is unchanged.

## Target and status

The target is not a finite-family substitute. It retains arbitrary, possibly infinite regular families of finite connected sources with unbounded sizes, native functions, the original EHN maps, unchanged old shadows, a relation-only precompact expansion, strong amalgamation with free old shadows, and the stated countability/universality/existential-completeness/Ramsey clauses under their original hypotheses.

The source-preserving component theorem below has a complete English proof without a family-size, source-size, finite-signature or function-free restriction. It yields an INTERMEDIATE expansion. Precompact compression of its maximal profiles is not proved. The companion adversarial note refutes the more optimistic claim that merely deleting dead folded observations makes the remaining semantic types finite. This document therefore does not certify the full lift theorem.

## 1. Native definitions

Full embeddings reflect all old relations and preserve entire native function fibres, including undefinedness in the nonempty-fibre convention. An EHN map preserves positive relation and function incidences and restricts to a FULL embedding on every irreducible full source substructure. Irreducibility is indecomposability under free amalgamation of proper full substructures; with functions it must not be replaced by a Gaifman-clique test.

For a closed set R, every output of a function applied to inputs in R belongs to R; this includes nullary outputs. Only closed sets induce native substructures. The Gaifman graph uses all positive relation tuples and function input-output incidences. Components after deleting R are components in the ORIGINAL Gaifman graph with R removed, not necessarily components in the Gaifman graph of the induced relational restriction.

Let K=Forb_EHN(F), where F is any family of finite sources. Let D=A ⊕_X B be an actual full native free amalgam. Rename so A∩B=X. All displayed sides and X are full closed substructures, and there is no positive incidence involving both A\X and B\X.

## 2. Closed-cut source decomposition

Fix one finite source S and an EHN map f:S→D. Put R=f⁻¹(X), S_A=f⁻¹(A\X), and S_B=f⁻¹(B\X). These are subsets of the original source carrier, not vertices of an image quotient.

**Lemma 2.1: R is closed.** If all inputs r̄ lie in R and y is a source function output at r̄, positivity gives f(y) in the corresponding target fibre at f(r̄). That input lies in X; because X is closed in D, f(y) lies in X. Thus y lies in R. The argument also applies to nullary functions. We have NOT asserted that the image f(S) is closed.

**Lemma 2.2: components outside R are side-pure.** A source Gaifman edge maps either to equality or to a target Gaifman edge, since its positive witnessing tuple is preserved. A vertex mapped to A\X and one mapped to B\X can neither coincide nor share a target positive incidence. Therefore no source edge crosses S_A and S_B. A path outside R stays on one side, so each component of G_S−R lies wholly in S_A or wholly in S_B.

**Lemma 2.3: full source decomposition.** For a component C of G_S−R, the sets P=R∪C and Q=S\C are closed. For P, an output of root-only inputs lies in R. Otherwise an input lies in C, and any nonroot output shares a positive function incidence with it, so lies in C. For Q the same reasoning excludes an output in C. Every positive relation or function tuple has its nonroot vertices in at most one component, since any two such vertices are Gaifman-adjacent. Hence S=S[P] ⊕_{S[R]} S[Q] is an actual native free amalgam, not merely a union of weak structures.

**Lemma 2.4: irreducible tests stay in a side.** If an irreducible full source test I met both private sides, its closed intersections with P and Q would give a free decomposition into two proper full substructures. This contradicts irreducibility. Intersections are closed, and the positive-tuple/free-fibre decomposition restricts correctly. Thus every irreducible test is contained in P or Q. The proof does not use ambient Gaifman cliques as a substitute for induced irreducibility.

## 3. Raw component observations

For each finite original source S∈F, each closed cut R⊆S, each component C of G_S−R and an enumeration r̄ of ALL of R, name the rooted native pattern P_{S,R,C}=(S[R∪C],r̄). On a target A the corresponding relation holds at a tuple ā iff there is an EHN map p:S[R∪C]→A with p(r̄)=ā.

Source roots are enumerated injectively, but their target tuple may repeat coordinates. This relation-only expansion retains the same carrier and all old relation/function interpretations. It is not asserted precompact. The source family is unchanged; neither saturation nor a finite list is substituted.

If the two canonical raw component expansions have a common FULL induced expansion on X, their observations agree on every tuple from X, including repeated tuples. This is the precise semantic transfer used below.

## 4. One-pass total transfer theorem

**Statement.** Suppose A and B agree on all component observations of the fixed finite source S over X. Every EHN f:S→D=A⊕_X B has an EHN replacement h:S→B that agrees with f on EVERY original source vertex already mapped into B, including X. The source remains literally S.

**Proof.** Use R,S_A,S_B from Section 2. For every left component C⊆S_A, restrict f to the full substructure S[R∪C]. Its image lies in A by side-purity. The restriction is EHN into A: its irreducible source tests are full tests in S, and their full image embeddings into D factor through the full target substructure A.

The roots map to an X-tuple. Equality of component observations produces an EHN map p_C:S[R∪C]→B agreeing with f on the ENTIRE R. There are finitely many left components. Choose such a map for each. Define h on a left component C by p_C and on R∪S_B by the original f. These definitions agree on overlaps R and all values lie in B.

Every positive incidence belongs to R plus at most one source component. Positivity is therefore supplied by p_C on a left component and by f factored into B on a right component or on R. By Lemma 2.4, every irreducible full test lies in R plus one component or wholly in R. There h agrees with an EHN map, so the test is embedded FULLY, reflecting negative old relations and preserving the complete native function fibres. Consequently h is EHN. Only left components changed, proving the asserted agreement on the entire original B-preimage. QED.

This one-pass argument needs no source-support minimizer or Claim 2 iteration once all component realizations are available. Alternatively, moving one nonempty left component C and fixing the complement gives the exact source-support decrease |g⁻¹(A\X)|=|f⁻¹(A\X)|−|C|. This connects directly to the existing native descent interface without changing its source count.

**Arbitrary-family corollary.** If A,B∈K share the full raw component expansion on X, their actual native free amalgam D belongs to K. Otherwise a finite original forbidden EHN witness S→D transfers to B, contradicting B∈K. This handles an unbounded infinite family one finite source at a time; there is no global size bound or root-image injectivity premise.

## 5. Maximal witnesses and strong amalgamation

A witness A containing a finite full old root X is maximal on X if every component observation on X is unchanged under every allowed full extension of A. It is maximal relative to extensions of that actual witness; unrelated extensions of X need not be compatible.

**Maximal free-amalgam witness.** If A and B share the raw profile on X, both are allowed, and A is maximal on X, the free amalgam D is allowed by the preceding corollary. It is NOW legitimate to apply maximality to A⊆D. The profile on X is unchanged. Every allowed extension of D is an allowed extension of A, so D is maximal on X as well. Proving D allowed comes first; maximality is not used circularly to certify D.

**Countable query construction.** If the component queries on fixed finite X have countably many representatives, enumerate them q_0,q_1,… . Starting at an allowed A_0⊇X, at stage n realize q_n in an allowed full extension if possible, and otherwise keep A_n. Take the union A_∞. It is allowed: a forbidden source is finite, so a putative EHN map into the union has image in one stage; fullness of that stage in the union factors the map EHN into the stage, a contradiction. If a query became newly realizable in an allowed extension of A_∞, it was already possible at its own stage and was realized then. Thus A_∞ is maximal on X.

This uses countability only where stated. A finite signature and finite sources up to isomorphism ensure it even for an infinite family. An arbitrary infinite signature need not have countably many finite source types. The full requested theorem must derive adequate effective countability or coding from its actual assumptions; it must not silently add a countability assumption here.

**Raw maximal-trace age.** Assuming the needed maximal extension operation, finite raw traces induced from maximizing witnesses are hereditary. Maximality on Y implies maximality on every closed subroot X⊆Y, since every query on X is also a query on Y.

To amalgamate finite traces Y*,Z* over full X*, choose maximizing witnesses A_Y,A_Z meeting only in X. Common expanded-root embeddings give equality of all raw queries on X. Thus D_0=A_Y⊕_X A_Z is allowed. Maximality of each witness preserves the old expanded profiles on its respective Y or Z. The finite old set Y∪Z is closed in D_0 and induces the free amalgam of the old sides. Extend D_0 to a witness maximal on Y∪Z. It still preserves both previous side profiles, and its finite trace on Y∪Z is a strong expanded amalgam with exactly the free old shadow. QED.

This establishes structural amalgamation for an intermediate possibly nonprecompact language. JEP is separate: connected forbidden sources plus compatible full empty roots give it; incompatible nullary diagrams do not become compatible merely because strong AP holds.

## 6. Dead observations and the missing compression

An observation is live if realized in some original allowed structure at any root tuple; otherwise it is dead. Dead predicates are constant false on allowed structures and all allowed full extensions. Removing them preserves root-profile agreement and maximality exactly. A pattern containing an original forbidden EHN witness is dead by EHN composition; a full forbidden core is one sufficient reason.

However the companion note proves that even a finite-signature, regular, printed-image-closed family can have INFINITELY MANY SEMANTICALLY DISTINCT LIVE FOLDED OBSERVATIONS OVER ONE OLD VERTEX. The cut patterns can even be genuine minimal-cut pieces of the ORIGINAL family. Therefore deleting dead observations does not yield precompactness by itself.

The narrower possible objective is a cofinal coherent compression of MAXIMAL profiles. It must be proved from the original regularity and image-closure assumptions, not installed as an additional premise. Such a proof must supply:

1. enough allowed extensions with stable profiles;
2. finite codes on each finite old root sufficient for the actual component-transfer theorem;
3. coherence under full embeddings, restrictions to closed subroots and root re-enumerations;
4. the arity-wise uniform finiteness needed for finitely many added symbols of each arity.

The live counterexample's displayed infinite distinctions disappear after one allowed blue-triangle extension, so it does not refute this maximal-profile objective. Neither does it prove it. This is the exact remaining precompactness problem, not a bounded-family replacement for the theorem.

For a finite relational old language, finite compatible stable-profile sets on each n-element old structure could be combined into a finite arity-n codebook, since there are finitely many labelled old diagrams. With an arbitrary infinite old signature, that uniformity requires a separate argument. Higher source arities with repeated target tuples must be represented by effective lower-root codes; they cannot be ignored when counting finite expansions.

## 7. Consequence checks and boundaries

If a cofinal coherent coding is established, the structural proof above transfers to the coded maximal traces. Only injective enumerations of finite closed roots need be named, so the finite codebooks give finite expansion fibres. Under the original countability hypotheses the Fraisse limit then follows. The finite-relational universal/existential-complete clause also needs compatible lifts over old finite roots; universality alone is not the existential-completeness proof. One must realize maximizing witnesses in the limit and use maximality to lift finite existential extensions compatibly over those roots.

Ramsey remains a separate construction under the original local-finiteness hypotheses. The corrected sparse-control equivalence is logically equivalent to the missing Ramsey conclusion, not an independent completion theorem. Strong AP and finite fibres do not establish it.

No claim is made that this intermediate expansion equals the printed distinct-root minimal-piece lift. The bounded saturation repair remains a special case, not the full target. No source-size bound, relational-only assumption, saturation-regularity hypothesis, or unproved sparse-control condition has been substituted for the original theorem's assumptions.

## 8. Independent checks after the English audit

A new finite partial-unary checker used true full-closed irreducibility, not Gaifman cliques. It tested all 533 source structures on at most three vertices against 80 native free-amalgam targets: 1,523,184 maps, 4,996 EHN maps, 8,076 component decompositions, 34,440 irreducible no-crossing checks, 4,124 valid right transfers with exact support decrease, and 3,704 simultaneous transfers. There were 144 irreducible source tests that were NOT Gaifman cliques. All tests passed. This is a bounded sanity check for a partial unary function, not a proof for every arity or a Lean certificate.

The companion live-profile checker passed 16 threshold cells, ten positive folded maps, 16 triangle-extension maps, 6,848 full singleton/edge tests, 36 minimal-cut restorations, and 18,852 small-deletion connectivity checks. Full results and exact script hashes accompany this English audit. The general mathematical proofs are independent of these finite executions.

## Source anchors

At repository snapshot 9bd06470cd55733d1aaf35927ef568fdadc2332e, the existing interfaces are GenericClosedComponentTransfer.lean, NonminimalClosedComponentFlip.lean, RootedTransferShadowAvoidance.lean, and FiniteClosedComponentTagLift.lean. Their conditional transfer mechanism supports Sections 2–5; it does not establish Section 6's compression objective. The original manuscript's distinct-root lift/image-closure definitions and the original flip argument remain the statement anchors. The older homomorphism-only theorem uses a finite signature and finite-TOTAL piece regularity, so it does not automatically settle the newer per-width EHN problem.
