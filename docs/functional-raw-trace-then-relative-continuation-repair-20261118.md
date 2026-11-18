# Two-stage functional repair: raw source-pattern lift, then finite continuation coding

18 November 2026. English-level proposed theorem with adversarial boundaries; NOT a Lean certificate or manuscript change.

## Stage I: unconditional strong AP without regularity

Let F be an arbitrary family of nonempty finite connected native L-structures; L may have partial functions. Let K=Forb_he(F). The old family is not semantically saturated.

For every S in F, take all induced FULL native **closed** substructures P<=S and all closed nonempty roots R<=P for which P is a root-attached component pattern: P is a native free amalgam of its root R and at most one nonroot connected component after deleting R. (If the closure of the Gaifman boundary includes nullary outputs, root connectivity is interpreted modulo the fixed nullary closure; no general nullary-JEP claim.) Record an added relation Q_(S,P,R) of arity |R|. On an allowed witness A, the relation holds at the tuple a iff there is a genuine EHN map P->A sending the ordered source R to a. **Allow repeated coordinates in the TARGET a.** All original functions are unchanged. For finite F the number of these patterns is finite even if the old signature is infinite.

One must close the pattern family under taking closed-root components of these P (recursively). Since each such P is an induced full substructure of an original finite S, doing this does not create infinitely many patterns for a finite F.

**Source decomposition:** for an EHN map f:S->D=A+_X B, the preimage of the FULL closed root X is closed in S. Every component of S minus this preimage is side-pure. The full root-boundary closure R_C=Cl_S(N_S(C)) is contained in f^-1(X), and P_C=S[R_C union C] is a full native substructure. Its map into the old side has all root images in X. Equality of these Q observations on X transfers the component into the other side. Native free-fold preserves irreducible source tests. Thus D avoids F. No source image is assumed function-closed and no weak quotient is used. This is covered conditionally by existing Lean modules GenericClosedComponentTransfer and RootedTransferShadowAvoidance, plus PR #1280's global bridge.

**Canonical trace stability:** the same transfer applies to any rooted pattern P whose root maps into A while a component of its image lies in B\\X. Transfer those B-only components to A; the entire source P and its root tuple are preserved. Because the chosen source-pattern family is closed under taking these component patterns, equality of Q on X suffices. Therefore the canonical raw trace expansion of D restricts EXACTLY to the canonical trace expansions of A and B.

Let K_raw^+ be the AGE of restrictions of canonical raw trace expansions of ALLOWED (finite or countable) witnesses. Then hereditary and exact shadows follow from definition; the free amalgam of witnesses with matching traces on X is an allowed witness inducing the exact free expanded amalgam on their old roots; hence K_raw^+ has strong AP with free old-language reduct. Disjoint union gives JEP for compatible empty/nullary diagrams. This is a candidate correction of the UNCONDITIONAL first clause of Theorem 3.17, with a DIFFERENT lift from the published distinct-root minimal-piece lift.

## Stage II: precompact sharp continuation quotient

The raw trace lift is generally nonprecompact for infinite F, because high-arity predicates may be nonconstant on repeated-coordinate target tuples. To compress, use relative continuation equivalence over each fixed allowed finite FULL closed old root X:

 A ~_X B iff for all finite allowed C>=X, [A+_X C in K iff B+_X C in K].

Finite index at each X is equivalent to existence of a precompact exact-shadow relation-only AP lift; a UNIFORM index bound over |X|=n is necessary and sufficient for the desired format with finitely many new diagonal-FREE relations of arity n. This avoids unrelated old-root-diagram inflation.

The finite-maximal-witness construction proves the sufficiency, using only finite allowed witnesses: type inclusion grows monotonically under extensions, so finite index ensures a finite maximal extension. Label each closed n-vertex root by its maximal continuation class; use only k(n) named predicates, indexed separately relative to the actual old root diagram. Equal maximal labels force allowed free amalgamation; maximality preserves all side labels. The old functions are unchanged.

When F is finite, Stage I source patterns are finite and already give a finite precompact AP expansion. The same source patterns give an explicit uniform bound on Stage II continuation classes even in infinite old functional languages. Irreducible forbidden sources contribute no crossing patterns; an irreducible family plus finite effective nonirreducible family has the same finite bound (CSS use).

## Adversarial points still requiring proof

- Canonical raw trace preservation for arbitrary rooted patterns P needs the explicit recursive closure under taking closed-root subpatterns. A naive collection of only MINIMAL original forbidden pieces is NOT enough. The complete source-faithful proof is English only; existing Lean modules cover the conditional transfer core but not the entire raw AGE AP conclusion.
- Do not drop repeated target-root coordinates in Stage I. The decorated C5 / ternary half counterexample tests exactly that failure.
- For functions of arity zero, a compatible fixed common nullary diagram/closure is needed before claiming JEP. Source boundaries can include zero-ary closure vertices that are not Gaifman-connected; use rooted component convention rather than claiming every root boundary induced substructure is connected.
- Exact-shadow finite-age claims do not imply a universal reduct for countable structures with infinite unary-function closure. The finite-relational omega-categorical conclusion requires its separate Fraisse/EC argument.
- The Stage II quotient is a NEW lift. Replacing only the old piece equivalence in the printed construction does not validate it.
- The Ramsey Theorem 3.23 additionally depends on a CORRECT native weak-size completion step of the partite argument. Its printed appeal to regularity for a finite F0 should be replaced by the already assumed local-finiteness size cutoff n(C0'), without asserting F0 is finite in arbitrary languages. Lemma 2.30's corrected weak-source/native-relational bridge is not yet fully Lean-certified.
- These two stages are not automatically a **minimal text patch**. The aim is mathematical correctness and preservation of the full functional scope. The one-hunk semantic-piece patch fails the irreducible-plus-finite CSS infinite-language example.

## Lean milestones

RAW-01: native source closed-component pullback and transfer (conditional theorem already merged).
RAW-02: raw pattern family closed under component restriction.
RAW-03: raw canonical trace preservation across free amalgam (NEW).
RAW-04: unconditional raw age hereditary/exact-shadow/free strong AP (NEW).
MAX-01: finite stable continuation profile from finite image (new Lean module in PR #1280, CI pending).
MAX-02: row restriction to smaller full roots and coherent finite indices.
MAX-03: free strong AP of finite maximal-relative-continuation lift.
RAM-01: correct local finiteness cutoff and original-function weak-size partite transfer.

No theorem-level Lean or manuscript validation marks claimed for RAW-02--04 or MAX-02--03.
