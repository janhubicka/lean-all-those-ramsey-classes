# Track B/C: right-exclusive target/source predicate equivalence

**14 November 2026.** Independent reusable native full-free-amalgam lemma;
the original numbered 2019 manuscript remains frozen.

Given an actual full native target free amalgam over root X
with target embeddings `jLeft` and `jRight`, its exact
overlap theorem proves the target images of the two root
embeddings coincide. Accordingly, for an arbitrary weak
source map `f` (which need NOT be injective),

```lean
x ∈ weakFreeRightPart (sL := iLeft) (iL := jLeft)
    (iR := jRight) f
  ↔ f x ∈ fullFreeRightExclusiveTarget iRight jRight
```

The first predicate is used by the verified positive-B-rank
geometric component/dichotomy theorem; the second by
actual strict B-exclusive SOURCE rank and active-boundary
support transport. The equivalence removes a subtle mismatch
when the NEW same-witness source of #1154 is used as the
next intermediate state.

Both directions explicitly use the true target free-amalgam
overlap; neither assumes global injectivity or the existence
of a valid positive-rank successor. This is not root reflection
for the selected Q-side map, and does not eliminate smaller-root
old-root capture/A-mixedness or prove the initial local
boundary injection.

Named #print axioms, protected active root, full module build,
source/contract/permitted-axiom/no-admission CI required.
