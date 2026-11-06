# Track C — full outer rooted profiles of arbitrary closed contexts

This theorem extracts the ACTUAL native functional algebraic content of the already checked specialized geometric outer-context congruence, without requiring the outer context to be a source minimal-closed-separator geometric piece.

Let
```
Old = OldInner +_U E,
New = NewInner +_U E
```
be TWO genuine original-language FULL functional free amalgams over exactly the same complete root and complement E. Let SR⊆E be ANY function-closed right-hand subset containing every embedded gluing-root vertex. Set `KOld = iOldInner(OldInner) ∪ iOldE(SR)`, `KNew = iNewInner(NewInner) ∪ iNewE(SR)`.

For ANY native full outer root `RootOuter` embedded in the induced `E|SR`, if the inner rooted extensions have the same forbidden-diagram all-test profile over U, then:

1. Both KOld and KNew are genuine function-closed native induced structures.
2. The outer root embeds FULLY into KOld and KNew, with literal original/new complement coordinates.
3. The two contexts have IDENTICAL complete rooted forbidden incompatibility profiles against **every** test attached over RootOuter.

Implementation `fullFreeAmalgam_closedContext_allTestProfile_equiv` uses the checked `fullFreeAmalgam_nestedContext_namedFullDiagram` to construct BOTH actual native contextual free-amalgam diagrams and the equality of their induced complete gluing-root embeddings, followed by `functionalActualContext_profile_equiv_of_inner_equiv` (both directions of native reassociation). No family-isomorphism-closure assumption, quotient image, arbitrary weak-map injectivity or original A-support minimality is added.

**Iteration significance.** Rooted all-test profile is an invariant of the *closed induced contextual diagram*, not of source minimal-cut geometry. This theorem can be combined with the single-source B→A flip and no-escape/rank conservation theorem PR #880 to keep the outer rooted profile even when the intermediate contextual carrier is not a genuine geometric minimal-cut piece.

**Still open:** ensure the original outer root (and all subsequent carried roots) remains embedded in the unchanged complete complement side for each chosen inner flip; show positive interior B-rank yields a partner/root-injective genuine inner piece (general root-collision and smaller mixed-root issues); provide a legal selected genuine geometric piece for terminal original-global canonical lift. In particular the theorem does not assert that a closed context is selected by the original 2019 piece relation.

Named axiom audit and retained root; exact-head Lean CI pending. Frozen 2019 manuscript prose unchanged.
