# The CSS application under relative-root regularity

17 November 2026. Focused English verification, NOT a Lean certificate of the CSS Ramsey theorem.

## Printed source and apparent infinitude

In HN19, the proof of Theorem 4.52 introduces an expanded language with the original finite relational symbols, finitely many new functions and orbit relations of each given arity, and functions F_{a,i} defined only on tuples of pairwise DISTINCT vertices. It then sets

- F1 = all ordered irreducible structures not in Age(U+);
- F2 = weakly ordered structures on at most M=N^(2^n) vertices without an EHN map to U+.

The printed assertion 'F2 is finite' is not literally automatic in this infinite language: on a one-element carrier, repeated-argument values for symbols F_{a,i} are syntactically possible at arbitrarily large a. However such structures are already excluded by F1 and need not be separately forbidden.

## Irreducible-incidence lemma

Let B be a finite weakly ordered structure avoiding F1. Every positive tuple of a NON-ORDER relation or a function domain with its output lies in a full closed substructure J that is irreducible in the shadow B^- (remove order). To obtain J choose a minimal closed subset containing the tuple's support (and the function output). If J were a free amalgam of two proper closed substructures, its positive incidence would be entirely on one side; this contradicts minimality. Thus J is irreducible in B^-.

By the DEFINITION of weakly ordered, every pair of distinct vertices of J is comparable in the reflexive acyclic relation <=; therefore <= is a linear order on J. Thus J is an ordered irreducible full L-structure. Since B avoids F1, J belongs to Age(U+).

In U+, every positive relation tuple and every function-domain tuple of arity a has pairwise distinct inputs (for the new symbols introduced by the proof). Hence NO such positive tuple of arity a>|B| can occur in B. For old symbols of bounded arity, no problem arises. Therefore, on structures B of size at most M avoiding F1, every new symbol of arity >M has EMPTY interpretation. Since the language has only finitely many new symbols of every arity <=M, there are only finitely many isomorphism types of such B.

Consequently F2 can be replaced WITHOUT CHANGING Forb_he(F1 union F2) by the **finite** subfamily

F2_eff = {B in F2 : B avoids F1},

up to isomorphism. Every member of F2\F2_eff is already excluded by a source from F1.

## Uniform continuation index

F1 consists of irreducible sources and therefore cannot map via EHN across a native full free amalgam. F2_eff is finite. Hence the original-source closed-cut pattern count T_{F2_eff}(n) from the companion note bounds continuation types uniformly for all finite full roots X of size n:

|Ext(X)/~_{F,X}| <= 2^T(n).

This resolves the PREVIOUS 'old-root-label inflation' failure in the proposed all-connected-piece equivalence; that equivalence must NOT be used for CSS. This check does not prove the whole CSS Ramsey theorem, the local-completion bound, or the existence of the claimed finite closure functions: those remain separate manuscript/Lean obligations.

## Adversarial qualifications

1. The minimal irreducible-incidence argument MUST be performed in the shadow B^- and then linearity of <= deduced using the weak-order definition. Treating an irreducible of the FULL ordered language as automatically irreducible without order is invalid.
2. The 'tuple is supported inside J' step must include native function outputs and use FULL closed substructures. Merely choosing the support of its input tuple can fail to be closed.
3. This step proves effective finiteness of bounded forbidden sources *modulo F1*, not that the literal displayed F2 set is finite.
4. If the expanded language has an additional family of symbols with no distinct-coordinate interpretation rule, show separately that only finitely many such symbols of arity <=M occur; the printed original relational language is finite.
5. Reverify the exact equation M=N^(2^n), closure bound and subsequent Section 4.4.2 Ramsey transfer independently. No claim of source-matched Lean certification is made.

Lean obligations: RCR-CSS-01 minimal closed irreducible shadow support; RCR-CSS-02 induced linear order under weakly ordered; RCR-CSS-03 high-arity vanishing; RCR-CSS-04 finite effective F2; RCR-CSS-05 finite-interface continuation theorem; RCR-CSS-06 original local-completion/Ramsey application.
