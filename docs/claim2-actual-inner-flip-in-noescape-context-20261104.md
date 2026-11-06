# Track C: actual B→A flip inside an arbitrary closed/no-escape outer context

Theorem: `claim2_actualRightFlip_in_closedNoEscapeContext`.

Let F be the original forbidden family, with finite actual source structures. Let Source∈F and f:Source→Target be a genuine EHN map into the original full native functional free amalgam of Left and Right with the common full original-global canonical lift. Fix an **arbitrary source vertex set K**—NOT assumed to be a geometric minimal-cut piece—with the following properties:

* K is closed under every native set-valued function;
* no Gaifman edge leaves K from a contextual vertex outside the entire shared-target-root preimage S;
* K contains the COMPLETE selected genuine inner source geometric piece d;
* d has positive root width, its selected component is B-only, its ordered root maps into the shared target root with injective images, and its selected component contains a B-exclusive **source** vertex.

Write Old=Inner+_U E for the literal native source free diagram. Because K contains all of Inner, its exact vertex set is `iOldInner(Inner) ∪ iOldE(SR)` for SR=`iOldE⁻¹(K)`. The closedness of K and full native embedding imply SR is closed; the full inner inclusion implies SR contains the complete inner gluing root U.

Apply the ORIGINAL full canonical B→A source replacement **once**. It produces one real F-member New=Q+_U E and EHN map flip unchanged on EVERY E vertex. For **the same** New,Q,iQ,iE,flip, the proof returns

1. New∈F and complete native functional free-amalgam source diagram.
2. `flip(iE b)=f(b.1)` for every b∈E (without a weak-image quotient).
3. `KNew=iQ(Q)∪iE(SR)` is function-closed.
4. KNew is no-escape relative to SNew, the new complete shared-target-root preimage, by the generic verified full-amalgam transfer.
5. `B_inside(KNew,flip) < B_inside(K,f)` in **source** cardinality.
6. `A_outside(KNew,flip) = A_outside(K,f)` exactly.

The support comparisons use the already independently checked generic native full-amalgam complement-bijection and local-rank arithmetic. No assumption that either K or KNew is a genuine minimal-separator geometric piece, no intermediate A-support minimality, no global weak-map injectivity, no source family isomorphism closure.

This addresses the *context transport* part of the iteration on a weaker state than the printed geometric-piece state. It is not yet the unrestricted positive-B-rank **existence** theorem: a genuine inner flippable d must still be found for each state. The general-root partner/collision/mixed smaller-root alternative (#864) remains open. Complete ALL-TEST profile transportation for arbitrary K and a legitimate final selected outer piece are also separate outstanding tasks; the original global canonical relation indexes genuine selected geometric pieces, not arbitrary closed contexts.

Frozen manuscript prose unchanged. Dedicated Lean build, retained root and `#print axioms` required before validation.
