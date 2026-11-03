# Track B: complete mathematical reduction of contextual profile congruence

**1 November 2026. Status: proof architecture, NOT a kernel-certified result.**
Relevant independent draft PRs: [#741](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/741) and [#746](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/746).
Neither should be merged until every Lean module and axiom audit is green.
This note does not alter the frozen manuscript; review-only TODO ATRC-069 remains open.

## Target theorem (pure full-native source calculus)

Fix a full native set-valued functional language L, an **arbitrary**
forbidden-family predicate F, and full structures S, T, R.
Let `sT: S -> T` and `rT: R -> T` be full embeddings.
Let M and M' be full rooted extensions of S which have identical
incompatibility profiles against **all** full S-rooted tests.

Let C and C' be *actual chosen* full free amalgams

    C  = M  +_S T,
    C' = M' +_S T.

Both become R-rooted extensions through their T-embeddings,
`R -> T -> C` and `R -> T -> C'`.

**Claim:** for **every** full R-rooted extension P,

    forbiddenDiagram_R(C, P) <-> forbiddenDiagram_R(C', P).

Equivalently, the entire fixed-R-root incompatibility profiles of
C and C' are equal.

This claim requires no inclusion relation between R and S, no weak
source map injection, no bound on arity, and **no F-isomorphism closure**:
all changes of rooted presentation below keep the original forbidden
whole source exactly as it was.

## Exact two-stage intermediate predicate

Use `forbiddenNestedFunctionalTestDiagram` from #746:

    nestedBad(M,T,R,P) :=
      exists Ext and a full Ext = T +_R P,
      such that forbiddenDiagram_S(M, Ext) holds,

where the S-root of Ext is the composite S -> T -> Ext.

The proved-in-source lemma (CI pending)
`forbiddenNestedFunctionalTestDiagram_iff_of_inner_equiv`
gives, for EVERY P,

    nestedBad(M,T,R,P) <-> nestedBad(M',T,R,P).

What remains is to establish, for each chosen C = M +_S T,

    forbiddenDiagram_R(C,P) <-> nestedBad(M,T,R,P).

### Forward: outer actual diagram -> nested actual diagram

Take a forbidden source W with full diagram `W=C +_R P`.
Since T embeds fully into C, its range is function-closed. The
induced vertex set

    ExtCarrier = image_W(P) U image_W(T)

is function-closed and contains the entire outer gluing-root.

The **symmetric named context** lemma of #741 exhibits its induced
full structure as `Ext=T +_R P`, with side carriers T and P,
FULL embeddings and exact coordinates. The originally established
diagram `C=M +_S T`, together with `W=C +_R P`, and the literal
inclusion `Ext -> W` now meets every premise of
`IsFreeAmalgam.reassociate_right` in partite-construction. Hence
`W=M +_S Ext`. The source W is still F-forbidden.

This is implemented as
`forbiddenOuterFunctionalDiagram_to_nestedTest` in #741,
with the resulting existential native nested diagram made explicit.
**Pending CI.**

### Reverse: nested actual diagram -> outer actual diagram

Take a forbidden source W with actual full diagrams
`Ext=T +_R P` and `W=M +_S Ext`.

1. Let `InnerCarrier=image_W(M) U image_W(T)`. The named
   inner-stage lemma `fullFunctionalFreeAmalgam_induce_innerStage`
   from #741 makes it function-closed and constructs the actual
   induced full diagram `Inner=M +_S T`, with full inclusion
   `Inner -> W` and exact T-coordinate preservation.
2. With this induced Inner and the full embeddings of Ext and P
   into W, `fullFunctionalFreeAmalgam_reassociate_right_reverse`
   from #746 proves the complete diagram `W=Inner +_R P`.
   Its hypotheses include exact agreement on the T and P vertices;
   they are supplied by the indicated induced embeddings.
3. The prescribed C and the induced Inner are full amalgams of
   the SAME M,T over the SAME S. Apply
   `freeAmalgamDiagram_unique` to obtain an onto FULL
   embedding e:C -> Inner respecting both M and T, hence
   respecting the entire R-root inside T.
4. Apply `freeAmalgam_precompose_left_iso` to `W=Inner +_R P`
   with e:C -> Inner. The resulting source diagram is literally
   `W=C +_R P` and F W still holds. Alternatively use the
   separately audited `forbiddenFunctionalDiagram_iff_of_ontoRootIso`
   from #746.

**No forbidden-isomorphism closure is used or needed in this
existential profile theorem**: every witness W is carried along,
not replaced by its isomorphic image. The older
`forbiddenNestedActualSource_iff_of_inner_profile_equiv`
does require image/isomorphism closure because it compares forbidden
status of two already chosen, rather than existential, whole sources.

### Final outer profile

Combine the two diagram equivalences and nested congruence:

    forbiddenDiagram_R(C,P)
      <-> nestedBad(M,T,R,P)
      <-> nestedBad(M',T,R,P)
      <-> forbiddenDiagram_R(C',P).

Then use `functionalDiagramPiece_equiv_iff` (or the certified
canonical-glue bridge) to obtain full outer-root profile equality.

## Geometric specialization to original Claim 2

The generic algebraic claim applies to the old and new *outer
contexts* if:

- the replaced inner piece's ENTIRE full root lies in the old
  outer context, and its selected private component is inside it;
- the chosen outer root R lies in the retained FULL T-complement,
  so both contextual full embeddings agree on the R structure;
- both contexts are genuinely full native amalgams of the inner
  piece with the retained T (the named diagrams in #741).

This proves their incompatibility profiles coincide, **provided
the generic target theorem is formalized**.

It still does **NOT** show that the transported new outer context
is the rooted source component of a *minimal closed separator*.
That needs Track A's opposite **complete generated boundary**
criterion, especially for incomparable old and inner cuts.
Only after that geometry is proved can the algebraic all-test
profile congruence be applied to the exact 2019 geometric piece
symbol. Finite local B-only support decrease then belongs to
Track C, not to this proof.

## Adversarial checks before closing ATRC-069

1. Ensure no proof uses only a relation/graph encoding or a
   homomorphism without whole-fibre reflection.
2. All roots have their **full** induced structure, not merely
   equal ordered vertex lists.
3. Prove both directions of context-to-nested equivalence, not
   just a one-sided implication.
4. Show the isomorphism `C ~= Inner` respects R through T.
5. Keep the named context and actual source distinct from an
   arbitrary existential gluing witness.
6. Run full Lean CI, `#print axioms`, active-root inventory and
   literal-source admission scans before marking any new item green.
7. Do not advertise a complete Claim 2 while the opposite generated
   boundary and finite iterative support argument remain open.
