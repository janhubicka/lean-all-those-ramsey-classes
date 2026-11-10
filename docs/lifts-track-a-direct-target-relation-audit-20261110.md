# 10 November 2026 — Track A target-relation simplification

The theorem `nestedGeometric_actualGlobalWitness_preserves_outerRelation`
has a genuine source-replacement conclusion and a seemingly
separate conclusion asserting the ORIGINAL older global canonical
relation in `Target`. The first part is the nontrivial part;
the second follows immediately from input data.

In the statement, `Old` is an actual finite forbidden native
functional source (`F Old`), `outer` is its genuine geometric
piece, `f : Old → Target` is an EHN weak homomorphism-embedding,
and the ORIGINAL outer root-image tuple is injective:

```lean
hOldOuterRootInjective :
  Function.Injective (fun i : Fin m => f (outer.roots i))
```

Therefore, BEFORE CONSTRUCTING ANY REPLACEMENT,

```lean
geometricGlobalCanonicalRelation_of_weak
  F Old (inferInstance : Finite V) hFOld outer hm
  Target f hf hOldOuterRootInjective
```

already proves the target relation at the exact original ordered
outer target tuple. No `New`, selected `Q`, old/new nested
piece class equality, or transport through `flip` is required
for that particular conclusion. The old 2019 global piece symbol
is already realized from the old forbidden geometric witness.

Consequently, the proposed [PR #969](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/969)
was **closed unmerged** after the independent audit: it packaged
an additional conjunct which was redundant given the theorem's
original hypotheses. A full Lean compilation of that proposal
does not make it a new mathematical result.

The current targeted cleanup replaces the approximately 50-line
target-relation transport segment in
`Lifts/NestedActualGlobalWitnessOuterRelation.lean` by this
one direct application. Its public theorem signature and
source flip construction are unchanged. The historical nested
geometric input is retained for backwards API compatibility,
although the direct proof does not need it.

**Do not confuse this simplification with solving the real gaps.**
The genuine Track A source-geometric preservation of the old
GLOBAL piece *symbol* across an actual selected-Q native full
source replacement remains nontrivial and already verified.
The original GLOBAL target relation cannot be realized at a
colliding root tuple (it includes injectivity by its semantics).
Track D owns that collision issue. Track C still needs existence
of a flippable B-only inner piece at each positive rank and the
correct terminal minimizer contradiction. No numbered manuscript
text is changed or previously removed TODO restored.

**Regression gate:** new exact-head pinned Lean compilation,
existing `CheckAxiomsNestedActualGlobalWitnessOuterRelation.lean`,
permitted axioms, no admissions, source-contract audit, and
active-root inventory. Historical refactor #964/#968 is
already verified and merged, separately from this cleanup.
