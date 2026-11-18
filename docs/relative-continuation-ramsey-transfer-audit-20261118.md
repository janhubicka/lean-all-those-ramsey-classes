# Ramsey transfer after correcting the homogenizing lift — exact audit

18 November 2026. Manuscript: `janhubicka/All-those-Ramsey-classes/ramsey.tex`, main blob `652d73b8896ca9884cb9f040d59c4804d63b5823`. This is a focused audit, **NOT** a kernel validation or a manuscript edit.

## Result 1: remove an incorrect attribution to regularity

In the printed proof of Theorem 3.23 (`thm:main`), immediately after the initial Ramsey/closure-picture construction, the text says:

> 'Now by the regularity of F there exists a finite F_0 such that every structure A in Forb(F_0) with a homomorphism-embedding to C'_0 is also in Forb(F).'

This is NOT an implication of any regularity used here. The hypothesis that supplies the stated BOUNDED SOURCE SIZE is the printed local-finiteness hypothesis, and the remark immediately after `thm:main` explicitly restates it in exactly these terms.

The correct use is:

> By the local finiteness assumption there exists n=n(C'_0) such that for every C not in Forb(F) with a homomorphism-embedding to C'_0 there is F in the original family of at most n vertices admitting a homomorphism-embedding into C. Apply the partite iteration n times.

No finite *subfamily* F_0 is required; in an infinite old language there may be infinitely many original forbidden types of size at most n. The partite proof uses the size cutoff, not a literal finite list. This statement change is local, preserves native functions, and does not need regularity.

## Result 2: the final bounded-source step is STILL a separate obligation

The printed `lem:iteratedpartitestep2` is stated for a RELATIONAL language with a closure description U and checks U-CLOSED substructures of U-size <=j. The proof of `thm:main` says 'the shadow of every substructure with at most n vertices has a completion', then concludes that no original forbidden EHN source of <=n vertices maps to the shadow.

For native partial functions the image of a finite source under a weak EHN map need NOT be function-closed. Therefore **small full closed substructures are insufficient by themselves** to cover all weak source tests of <=n vertices. The point must be reconciled with `prop:closures` (the native-to-relational-closure interpretation) and the source-matched weak-test form of local completion.

The current manuscript's Lean markers for the full iterated partite increment `ATRC-009/016/018/019/020/021/022` still signal open or conditional components. The corrected finite-age continuation lift cannot automatically close them. Consequently **the new homogenization proof does not yet certify Theorem 3.23**.

A source-faithful proof should either:
(a) establish the exact weak-size <=n coverage of the corrected partite construction and transport it back through `Rel`; or
(b) replace the step with the already proved coordinated weak-substructure completion framework, including every needed hypothesis and support bound.
Neither is supplied by a finite continuation-index argument alone.

## Result 3: new lift dependency interface for Ramsey

What is already provided by a relative-root continuation lift (subject to kernel validation):
1. finite extensions have finite maximal witnesses;
2. old partial functions are unchanged;
3. the lifted age is hereditary with strong amalgamation and free old-language shadows;
4. uniform root index gives finitely many diagonal-free new predicates per arity.

For the original iteration, a finite *maximal lift of a witness of B* exists by first maximizing the original finite B-root and then maximizing the resulting finite witness carrier. The old B-root labels remain fixed under that second extension. Therefore the 'overline B' construction does not require countably saturated witnesses.

The final 'maximal lift C' construction also exists as a FINITE maximal witness, but **only after** the old shadow of C_n has been proved forbidden-free using the correct weak/local-completion conditions.

The transfer from the Ramsey arrow on C_n to the corrected lift needs a source-matched check that embeddings of `overline B` preserve the exact continuation labels, not just an arbitrary assignment of new predicates.

## Result 4: applications and sharpness

- For finite original F, choose n=max |F| in the old-source boundedness step, regardless of whether the function signature is infinite. The fixed-root continuation index is uniformly finite by the original-source finite-cut query table. This supports a functional finite-family homogenization statement, *not* automatic Ramsey.
- For the CSS application, the irreducible family F1 cannot create crossing forbidden maps; the bounded F2 family can be replaced by finite effective F2 after checking all high-arity positive incidences are excluded by F1. The weak-order minimal closed irreducible support is the delicate lemma; its Lean verification is still missing.
- The conditional infinite Gamma_m obstruction forces infinitely many relative continuation classes on the SAME singleton, and therefore still violates the new regularity condition.
- The old all-connected-piece semantic relation is too strong in infinite signatures because it counts old root diagrams. The relative continuation relation avoids this inflation.

## Re-verification marks

RCR-RAM-01: repair attribution to local finiteness and use size cutoff n(C'_0), not finite F0. ENGLISH_VERIFIED / EDITORIAL_PATCH_AVAILABLE.

RCR-RAM-02: native functional versus relational U-closed weak-size conversion in `lem:iteratedpartitestep2`. OPEN.

RCR-RAM-03: effective weak forbidden map supported on <=n source vertices after corrected partite iteration. OPEN.

RCR-RAM-04: preservation of maximal continuation labels of B and C in the iterated picture argument. CONDITIONAL ENGLISH, NEEDS_LEAN.

RCR-RAM-05: transfer of lift property and final Ramsey arrow under the new expansion. OPEN.

RCR-RAM-06: CSS weakly ordered irreducible support and effective F2 finiteness. NEW_ENGLISH_ARGUMENT, NEEDS_LEAN.

NO green theorem-level validation markers were added to the frozen manuscript. Old conditional Lean endpoints are not retrospectively elevated.
